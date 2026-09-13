import tkinter as tk
from tkinter import filedialog, simpledialog, colorchooser, messagebox
from PIL import Image, ImageTk, ImageDraw, ImageFont
import math
import copy
import json
import io
import base64
import time
import os
import sys

def resource_path(relative_path):
    try:
        base_path = sys._MEIPASS
    except AttributeError:
        base_path = os.path.dirname(os.path.abspath(__file__))

    return os.path.join(base_path, relative_path)
    
class UltimateImageEditor:
    def __init__(self, root):
        self.root = root
        self.root.title("PYINT")
        self.root.geometry("1400x850")
        self.root.minsize(1100, 700)

        self.THEMES = {
            "dark": {
                "bg_dark": "#0f1117", "bg_medium": "#161b22", "bg_light": "#21262d",
                "bg_card": "#1c2128", "accent": "#e94560", "accent_light": "#ff6b81",
                "accent_dark": "#c0392b", "text": "#e6edf3", "text_secondary": "#8b949e",
                "success": "#3fb950", "warning": "#d29922", "shadow": "#010409",
                "canvas": "#0d1117", "border": "#30363d", "hover": "#30363d",
            },
            "light": {
                "bg_dark": "#f0f2f5", "bg_medium": "#ffffff", "bg_light": "#e8ecf1",
                "bg_card": "#f7f8fa", "accent": "#e11d48", "accent_light": "#fb7185",
                "accent_dark": "#be123c", "text": "#1f2937", "text_secondary": "#6b7280",
                "success": "#16a34a", "warning": "#d97706", "shadow": "#d1d5db",
                "canvas": "#e5e7eb", "border": "#d1d5db", "hover": "#dbe3ee",
            },
        }
        self.theme_name = "dark"
        self.colors = dict(self.THEMES["dark"])
        self.root.configure(bg=self.colors["bg_dark"])
        self._themed_widgets = []  # (widget, role) role: frame|label|button|accent|list|canvas|status
        self._hover_jobs = {}
        
        # Varsayılan boş sayfa
        self.original_image = Image.new("RGBA", (800, 600), (255, 255, 255, 255))
        self.tk_image = None        
        self.scale = 1.0            
        self.history = []
        self.redo_stack = []
        self.cached_bg = None
        self.cached_scale = None

        self.selection_rect = None
        self.handle_rects = []
        self.resize_handle = None

        self.pan_x = 0
        self.pan_y = 0
        self.is_panning = False
        self.pan_start_x = 0
        self.pan_start_y = 0

        self.clipboard = None

        self.outline_color = "#e94560"  
        self.fill_color = ""        
        self.thickness = tk.IntVar(value=3)   
        self.font_size = tk.IntVar(value=24)  
        self.opacity = tk.IntVar(value=100)
        self._default_thickness = 3
        self._default_font_size = 24
        self._default_opacity = 100
        self._default_outline = "#e94560"
        self._default_fill = ""  # yok
        self.style_clipboard = None  # stil kopyala/yapıştır
        
        self._suspend_prop_trace = False
        self.thickness.trace_add("write", self.on_property_changed)
        self.font_size.trace_add("write", self.on_property_changed)
        self.opacity.trace_add("write", self.on_property_changed)

        self.action = None
        self.objects = []
        self.selected_obj = None
        self.selected_objs = []  # toplu seçim
        self._marquee = None  # ekran koordinatları (x1,y1,x2,y2) veya None
        self.groups = {}  # gid -> {"id", "name"}
        self.group_counter = 1
        
        self.layers = [{"id": 0, "name": "Katman 1", "visible": True}]
        self.current_layer_id = 0
        self.layer_counter = 1

        self.start_x = None
        self.start_y = None
        self.temp_items = []  
        self.rendered_objects_img = None
        self.drag_items = []
        self.snap_threshold_px = 6
        self.snap_guide_color = "#00e5ff"
        self._guide_items = []

        # Standart viewport cache: etkileşimde ucuz dönüşüm, idle'da HQ render
        self._hq_pil = None          # son yüksek kalite PIL (RGBA, canvas bg üzerinde)
        self._hq_scale = None
        self._zoom_after_id = None
        self._interaction_mode = False  # zoom/pan sırasında True
        self.dirty = False
        self.project_path = None
        # Kenar tutamaçlı kırpma: {'mode':'page'|'image', 'l','t','r','b', 'obj': optional}
        self.edge_crop = None
        self.edge_crop_handle = None

        self.setup_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.root.after(80, self._polish_ui)
        # Canvas boyutunu al ve ilk çizimi yap
        self.root.after(120, self.initial_draw)

    def initial_draw(self):
        """İlk çizimi yap"""
        self.root.update_idletasks()
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw > 1 and ch > 1 and self.original_image:
            iw, ih = self.original_image.size
            self.scale = min((cw - 40) / max(1, iw), (ch - 40) / max(1, ih), 1.0)
            self._initial_scale = self.scale
        self.redraw()


    def _polish_ui(self):
        """Hover animasyonları ve modern dokunuşlar."""
        self._bind_hover_recursive(self.root)
        self._status_pulse_step = 0

    def _bind_hover_recursive(self, widget):
        try:
            children = widget.winfo_children()
        except Exception:
            return
        for ch in children:
            cls = ch.winfo_class()
            if cls == "Button":
                self._attach_button_hover(ch)
            self._bind_hover_recursive(ch)

    def _attach_button_hover(self, btn):
        if getattr(btn, "_hover_bound", False):
            return
        # Renk örnekleri (snap/çizgi/dolgu): hover ile renk kaybolmasın
        if getattr(btn, "_is_color_swatch", False):
            btn._hover_bound = True
            return
        btn._hover_bound = True
        try:
            base_bg = btn.cget("bg")
            base_fg = btn.cget("fg")
        except Exception:
            return

        def on_enter(e, b=btn, bg=base_bg):
            try:
                if str(b.cget("state")) == "disabled":
                    return
                if getattr(b, "_is_color_swatch", False):
                    return
                hover = self.colors.get("hover") or self.colors["bg_light"]
                cur = b.cget("bg")
                if cur == self.colors["accent"] or cur == self.colors.get("accent_dark"):
                    b.configure(bg=self.colors["accent_light"])
                else:
                    b.configure(bg=hover)
            except Exception:
                pass

        def on_leave(e, b=btn, bg=base_bg, fg=base_fg):
            try:
                if getattr(b, "_is_color_swatch", False):
                    return
                if getattr(b, "_is_accent", False):
                    b.configure(bg=self.colors["accent"], fg="white")
                else:
                    b.configure(bg=self.colors["bg_light"], fg=self.colors["text"])
            except Exception:
                pass

        btn.bind("<Enter>", on_enter, add="+")
        btn.bind("<Leave>", on_leave, add="+")

    def toggle_theme(self):
        self.theme_name = "light" if self.theme_name == "dark" else "dark"
        self.apply_theme(self.theme_name)
        label = "🌙 Karanlık" if self.theme_name == "light" else "☀️ Açık"
        try:
            # ayarlar butonu metnini değiştirme
            if getattr(self, "btn_theme", None) is not getattr(self, "btn_settings", None):
                self.btn_theme.config(text=label)
        except Exception:
            pass
        self.status_label.config(
            text=f"{'☀️ Açık' if self.theme_name == 'light' else '🌙 Karanlık'} tema",
            fg=self.colors["success"],
        )
        self._animate_status()

    def apply_theme(self, name):
        if name not in self.THEMES:
            return
        self.theme_name = name
        self.colors = dict(self.THEMES[name])
        c = self.colors
        try:
            self.root.configure(bg=c["bg_dark"])
        except Exception:
            pass

        def walk(w):
            try:
                cls = w.winfo_class()
            except Exception:
                return
            try:
                if cls in ("Frame", "TFrame", "Labelframe"):
                    # canvas çerçevesi vs
                    cur = w.cget("bg") if "bg" in w.keys() else ""
                    # kaba sınıflandırma
                    if cur in ("#1a1a2e", "#16213e", "#0f1117", "#161b22", "#f0f2f5", "#ffffff",
                               c["bg_dark"], c["bg_medium"], c["bg_card"], c["bg_light"]):
                        pass
                    bg = c["bg_medium"]
                    # sağ panel card
                    if hasattr(self, "right_panel") and w == self.right_panel:
                        bg = c["bg_card"]
                    elif hasattr(self, "main_container") and w == self.main_container:
                        bg = c["bg_dark"]
                    elif hasattr(self, "canvas_frame") and w == self.canvas_frame:
                        bg = c["bg_dark"]
                    elif hasattr(self, "status_bar") and w == self.status_bar:
                        bg = c["bg_medium"]
                    else:
                        # parent zincirine bak
                        bg = c["bg_medium"]
                    try:
                        w.configure(bg=bg)
                    except Exception:
                        pass
                elif cls == "Label":
                    try:
                        w.configure(bg=w.master.cget("bg") if w.master else c["bg_medium"],
                                    fg=c["text_secondary"] if "secondary" in str(w.cget("text")).lower() or len(str(w.cget("text"))) < 12
                                    else c["text"])
                        # force readable
                        w.configure(fg=c["text"])
                        try:
                            w.configure(bg=w.master.cget("bg"))
                        except Exception:
                            w.configure(bg=c["bg_medium"])
                    except Exception:
                        pass
                elif cls == "Button":
                    try:
                        if getattr(w, "_is_accent", False):
                            w.configure(bg=c["accent"], fg="white",
                                        activebackground=c["accent_dark"], activeforeground="white")
                        elif w is getattr(self, "btn_theme", None):
                            w.configure(bg=c["bg_light"], fg=c["text"],
                                        activebackground=c["accent"], activeforeground="white")
                        else:
                            w.configure(bg=c["bg_light"], fg=c["text"],
                                        activebackground=c["accent"], activeforeground="white")
                    except Exception:
                        pass
                elif cls == "Listbox":
                    try:
                        w.configure(bg=c["bg_light"], fg=c["text"],
                                    selectbackground=c["accent"], selectforeground="white",
                                    highlightbackground=c["border"])
                    except Exception:
                        pass
                elif cls == "Scale":
                    try:
                        w.configure(bg=c["bg_medium"], fg=c["text"],
                                    troughcolor=c["bg_light"], highlightbackground=c["bg_medium"])
                    except Exception:
                        pass
                elif cls == "Canvas":
                    try:
                        w.configure(bg=c["canvas"], highlightbackground=c["border"])
                    except Exception:
                        pass
                elif cls == "Entry":
                    try:
                        w.configure(bg=c["bg_light"], fg=c["text"],
                                    insertbackground=c["text"],
                                    highlightbackground=c["border"])
                    except Exception:
                        pass
            except Exception:
                pass
            try:
                for ch in w.winfo_children():
                    walk(ch)
            except Exception:
                pass

        walk(self.root)
        # kritik widgetlar
        try:
            self.canvas.configure(bg=c["canvas"])
        except Exception:
            pass
        try:
            self.status_label.configure(bg=c["bg_medium"], fg=c["success"])
        except Exception:
            pass
        try:
            self.btn_outline_color.configure(bg=self.outline_color)
        except Exception:
            pass
        try:
            if self.fill_color:
                self.btn_fill_color.configure(bg=self.fill_color)
            else:
                self.btn_fill_color.configure(bg="gray")
        except Exception:
            pass
        try:
            self.btn_snap_color.configure(bg=self.snap_guide_color)
        except Exception:
            pass
        # yeniden hover bağla
        self._bind_hover_recursive(self.root)
        # canvas arka plan yeniden çiz
        try:
            self.redraw()
        except Exception:
            pass

    def _animate_status(self):
        """Status satırında hafif vurgu animasyonu."""
        if not hasattr(self, "status_label"):
            return
        steps = [self.colors["success"], self.colors["accent_light"], self.colors["success"]]

        def tick(i=0):
            if i >= len(steps):
                return
            try:
                self.status_label.configure(fg=steps[i])
            except Exception:
                return
            self.root.after(90, lambda: tick(i + 1))

        tick(0)


    def _attach_tooltip(self, widget, text, delay_ms=550):
        """Hover sonrası gecikmeli ipucu (rahatsız etmesin diye ~0.55 sn)."""
        tip = {"win": None, "job": None}

        def hide(_event=None):
            if tip["job"] is not None:
                try:
                    self.root.after_cancel(tip["job"])
                except Exception:
                    pass
                tip["job"] = None
            if tip["win"] is not None:
                try:
                    tip["win"].destroy()
                except Exception:
                    pass
                tip["win"] = None

        def show():
            tip["job"] = None
            if tip["win"] is not None:
                return
            try:
                if not widget.winfo_exists():
                    return
            except Exception:
                return
            tw = tk.Toplevel(self.root)
            tw.wm_overrideredirect(True)
            tw.attributes("-topmost", True)
            try:
                x = widget.winfo_rootx() + 8
                y = widget.winfo_rooty() + widget.winfo_height() + 6
            except Exception:
                x, y = 50, 50
            tw.geometry(f"+{x}+{y}")
            fr = tk.Frame(tw, bg="#1c1c1c", bd=0, highlightthickness=1, highlightbackground="#e94560")
            fr.pack()
            tk.Label(
                fr, text=text, bg="#1c1c1c", fg="#ffffff",
                font=("Segoe UI", 9), padx=8, pady=5, justify=tk.LEFT,
            ).pack()
            tip["win"] = tw

        def schedule(_event=None):
            hide()
            tip["job"] = self.root.after(delay_ms, show)

        widget.bind("<Enter>", schedule, add="+")
        widget.bind("<Leave>", hide, add="+")
        widget.bind("<ButtonPress>", hide, add="+")


    def _toggle_left_dock_pin(self):
        self._left_dock_pinned = not getattr(self, "_left_dock_pinned", False)
        try:
            if self._left_dock_pinned:
                self._btn_pin_left.config(text="📌 Sabitli", bg=self.colors["accent"], fg="white")
                self._set_left_dock(True)
            else:
                self._btn_pin_left.config(text="📌 Sabitle", bg=self.colors["bg_light"], fg=self.colors["text"])
        except Exception:
            pass

    def _cancel_left_hide(self):
        aid = getattr(self, "_left_hide_after", None)
        if aid:
            try:
                self.root.after_cancel(aid)
            except Exception:
                pass
            self._left_hide_after = None

    def _schedule_left_hide(self):
        if getattr(self, "_left_dock_pinned", False):
            return
        self._cancel_left_hide()
        self._left_hide_after = self.root.after(350, lambda: self._set_left_dock(False))

    def _on_global_motion_left_dock(self, event):
        try:
            rx = self.root.winfo_rootx()
            x = event.x_root - rx
        except Exception:
            return
        # sol kenar 12px: göster
        if x <= 12:
            self._cancel_left_hide()
            self._set_left_dock(True)
        elif not getattr(self, "_left_dock_pinned", False):
            # panel dışındaysa gizle zamanla
            try:
                if self._left_shell.winfo_ismapped():
                    lx = self._left_shell.winfo_rootx()
                    lw = self._left_shell.winfo_width()
                    if event.x_root > lx + lw + 8:
                        self._schedule_left_hide()
            except Exception:
                pass

    def _set_left_dock(self, show):
        """Sol paneli kaydırarak aç/kapa."""
        if getattr(self, "_left_dock_pinned", False) and not show:
            return
        target = self._left_dock_w if show else 0
        self._left_dock_target = target
        self._left_dock_visible = bool(show)
        if self._left_dock_anim:
            try:
                self.root.after_cancel(self._left_dock_anim)
            except Exception:
                pass
            self._left_dock_anim = None
        self._animate_left_dock()

    def _animate_left_dock(self):
        shell = getattr(self, "_left_shell", None)
        if shell is None:
            return
        try:
            cur = int(shell.winfo_width())
        except Exception:
            cur = 0
        target = int(getattr(self, "_left_dock_target", 0))
        if abs(cur - target) <= 2:
            shell.configure(width=target)
            self._left_dock_anim = None
            return
        step = max(8, abs(target - cur) // 4)
        if cur < target:
            cur = min(target, cur + step)
        else:
            cur = max(target, cur - step)
        shell.configure(width=cur)
        self._left_dock_anim = self.root.after(16, self._animate_left_dock)

    def setup_ui(self):
        main_container = tk.Frame(self.root, bg=self.colors["bg_dark"])
        self.main_container = main_container
        main_container.pack(fill=tk.BOTH, expand=True)
        
        btn_style = {
            "bg": self.colors["bg_light"], "fg": self.colors["text"],
            "padx": 10, "pady": 4, "cursor": "hand2",
            "font": ("Segoe UI", 9, "bold"), "relief": "flat", "borderwidth": 0,
            "activebackground": self.colors["accent"], "activeforeground": "white",
        }
        btn_accent = {
            **btn_style,
            "bg": self.colors["accent"], "fg": "white",
            "activebackground": self.colors["accent_dark"],
        }

        # —— İnce üst şerit ——
        top_wrap = tk.Frame(main_container, bg=self.colors["bg_medium"])
        top_wrap.pack(fill=tk.X, pady=(0, 2))
        bar = tk.Frame(top_wrap, bg=self.colors["bg_medium"])
        bar.pack(fill=tk.X, padx=6, pady=4)

        # Sol üst: Proje | Ayarlar | Hızlı araçlar
        self.btn_project = tk.Button(
            bar, text="📁 Proje ▾", command=self.show_project_menu, **btn_style
        )
        self.btn_project.pack(side=tk.LEFT, padx=3)
        self._attach_tooltip(self.btn_project, "Dosya işlemleri")

        self.btn_settings = tk.Button(
            bar, text="⚙ Ayarlar ▾", command=self.show_settings_menu, **btn_style
        )
        self.btn_settings.pack(side=tk.LEFT, padx=3)
        self._attach_tooltip(self.btn_settings, "Tema, snap rengi, lisans")
        self.btn_theme = self.btn_settings

        self.btn_quick = tk.Button(
            bar, text="⚡ Hızlı araçlar ▾", command=self.show_quick_tools_menu, **btn_style
        )
        self.btn_quick.pack(side=tk.LEFT, padx=3)
        self._attach_tooltip(self.btn_quick, "Döndür, ayna, katman sırası")

        b = tk.Button(bar, text="🔍 Zoom", command=lambda: self.set_action("zoom_region"), **btn_style)
        b.pack(side=tk.LEFT, padx=3)
        self._tool_buttons = getattr(self, "_tool_buttons", {})
        self._tool_buttons["zoom_region"] = b
        self._attach_tooltip(b, "Bölge Zoom\nKısayol: Z")

        b = tk.Button(bar, text="📷 Ekran", command=self.capture_screenshot_region, **btn_style)
        b.pack(side=tk.LEFT, padx=3)
        self._attach_tooltip(b, "Ekran görüntüsü\nKısayol: F9")

        right_act = tk.Frame(bar, bg=self.colors["bg_medium"])
        right_act.pack(side=tk.RIGHT)
        b = tk.Button(right_act, text="⌨ Kısayollar", command=self.show_shortcuts_help, **btn_style)
        b.pack(side=tk.LEFT, padx=3)
        self._attach_tooltip(b, "Tüm kısayollar\nKısayol: F1")

        # —— Sol panel (sürekli açık) ——
        self._left_dock_w = 212
        self._left_dock_pinned = True
        self._left_dock_visible = True
        self._left_shell = tk.Frame(main_container, bg=self.colors["bg_card"], width=212)
        self.left_panel = self._left_shell
        self._left_shell.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 0), pady=2)
        self._left_shell.pack_propagate(False)

        left_inner = tk.Frame(self._left_shell, bg=self.colors["bg_card"], width=self._left_dock_w)
        left_inner.pack(fill=tk.BOTH, expand=True)
        left_inner.pack_propagate(False)

        self._tool_buttons = {}
        self._accordion_bodies = {}
        tool_tips = {
            "move": "Seç / Taşı\nKısayol: V veya H",
            "pen": "Fırça\nKısayol: B",
            "text": "Metin\nKısayol: X",
            "fill": "Doldur\nKısayol: G veya F",
            "eyedropper": "Renk Al\nKısayol: I",
            "crop": "Kırp\nKısayol: K",
            "zoom_region": "Bölge Zoom\nKısayol: Z",
            "rect": "Dikdörtgen\nKısayol: R",
            "square": "Kare\nKısayol: U",
            "circle": "Daire\nKısayol: O",
            "hexagon": "Altıgen\nKısayol: P",
            "star": "Yıldız\nKısayol: W",
            "callout": "Callout\nKısayol: L",
            "triangle": "Üçgen\nKısayol: T",
            "curve": "Eğri\nKısayol: C",
            "arrow": "Ok\nKısayol: A",
            "arrow_path": "Ok yolu\nKısayol: Q",
        }

        def _mk_accordion(parent, title, key, open_default=True):
            wrap = tk.Frame(parent, bg=self.colors["bg_card"])
            wrap.pack(fill=tk.X, padx=4, pady=(4, 0))
            hdr = tk.Button(
                wrap, text=("▼ " if open_default else "▶ ") + title,
                anchor="w", relief="flat", cursor="hand2",
                bg=self.colors["bg_medium"], fg=self.colors["text"],
                font=("Segoe UI", 10, "bold"), padx=8, pady=6,
            )
            hdr.pack(fill=tk.X)
            body = tk.Frame(wrap, bg=self.colors["bg_card"])
            if open_default:
                body.pack(fill=tk.X, padx=4, pady=4)
            self._accordion_bodies[key] = {
                "body": body, "hdr": hdr, "open": open_default, "title": title,
            }

            def toggle(k=key):
                info = self._accordion_bodies[k]
                if info["open"]:
                    info["body"].pack_forget()
                    info["hdr"].config(text="▶ " + info["title"])
                    info["open"] = False
                else:
                    info["body"].pack(fill=tk.X, padx=4, pady=4)
                    info["hdr"].config(text="▼ " + info["title"])
                    info["open"] = True
            hdr.config(command=toggle)
            return body

        scroll_host = tk.Frame(left_inner, bg=self.colors["bg_card"])
        scroll_host.pack(fill=tk.BOTH, expand=True)
        # basit dikey yığın (küçük ekranda taşabilir)
        shape_body = _mk_accordion(scroll_host, "⬛ Şekiller", "shapes", True)
        for text, action in [
            ("⬜ Dikdörtgen", "rect"), ("⬛ Kare", "square"),
            ("⭕ Daire", "circle"), ("⬡ Altıgen", "hexagon"),
            ("⭐ Yıldız", "star"), ("💬 Callout", "callout"),
            ("🔺 Üçgen", "triangle"), ("〰 Eğri", "curve"),
            ("↗ Ok", "arrow"), ("↩ Ok Yol", "arrow_path"),
        ]:
            b = tk.Button(shape_body, text=text, command=lambda a=action: self.set_action(a), **btn_style)
            b.pack(fill=tk.X, pady=1)
            self._tool_buttons[action] = b
            if action in tool_tips:
                self._attach_tooltip(b, tool_tips[action])

        tool_body = _mk_accordion(scroll_host, "🛠 Araçlar", "tools", True)
        for text, action in [
            ("✋ Seç", "move"), ("🖊 Fırça", "pen"), ("🔤 Metin", "text"),
            ("🪣 Doldur", "fill"), ("💧 Renk Al", "eyedropper"),
            ("✂ Kırp", "crop"),
        ]:
            b = tk.Button(tool_body, text=text, command=lambda a=action: self.set_action(a), **btn_style)
            b.pack(fill=tk.X, pady=1)
            self._tool_buttons[action] = b
            if action in tool_tips:
                self._attach_tooltip(b, tool_tips[action])




        right_panel = tk.Frame(main_container, bg=self.colors["bg_card"], width=288)
        self.right_panel = right_panel
        right_panel.pack(side=tk.RIGHT, fill=tk.Y, padx=(0, 2), pady=2)
        right_panel.pack_propagate(False)

        # —— Stil paneli (şekil seçilince görünür) ——
        self._style_panel = tk.Frame(right_panel, bg=self.colors["bg_card"])
        # başlangıçta gizli
        sp = self._style_panel
        sh = tk.Frame(sp, bg=self.colors["bg_medium"])
        sh.pack(fill=tk.X)
        tk.Label(
            sh, text="🎨 Stil", bg=self.colors["bg_medium"], fg=self.colors["text"],
            font=("Segoe UI", 10, "bold"),
        ).pack(side=tk.LEFT, padx=8, pady=6)

        self._style_row_outline = tk.Frame(sp, bg=self.colors["bg_card"])
        cf = self._style_row_outline
        cf.pack(fill=tk.X, padx=8, pady=4)
        tk.Label(cf, text="Çizgi", bg=self.colors["bg_card"], fg=self.colors["text"], font=("Segoe UI", 9)).pack(side=tk.LEFT)
        self.btn_outline_color = tk.Button(
            cf, bg=self.outline_color, width=3, height=1, relief="flat",
            command=self.choose_outline_color, cursor="hand2",
            activebackground=self.outline_color, highlightthickness=0,
        )
        self.btn_outline_color._is_color_swatch = True
        self.btn_outline_color.pack(side=tk.LEFT, padx=6)

        self._style_row_font_color = tk.Frame(sp, bg=self.colors["bg_card"])
        fcr = self._style_row_font_color
        fcr.pack(fill=tk.X, padx=8, pady=2)
        tk.Label(fcr, text="Yazı rengi", bg=self.colors["bg_card"], fg=self.colors["text"], font=("Segoe UI", 9)).pack(side=tk.LEFT)
        self.btn_font_color = tk.Button(
            fcr, bg=self.outline_color, width=3, height=1, relief="flat",
            command=self.choose_label_color, cursor="hand2",
            activebackground=self.outline_color, highlightthickness=0,
        )
        self.btn_font_color._is_color_swatch = True
        self.btn_font_color.pack(side=tk.LEFT, padx=6)
        self._attach_tooltip(self.btn_font_color, "Şekil / metin yazı rengi")

        self._style_row_fill = tk.Frame(sp, bg=self.colors["bg_card"])
        cf2 = self._style_row_fill
        cf2.pack(fill=tk.X, padx=8, pady=2)
        tk.Label(cf2, text="Dolgu", bg=self.colors["bg_card"], fg=self.colors["text"], font=("Segoe UI", 9)).pack(side=tk.LEFT)
        self.btn_fill_color = tk.Button(
            cf2, bg="gray", text="Yok", fg="white", width=5, relief="flat",
            command=self.choose_fill_color, cursor="hand2",
            activebackground="gray", highlightthickness=0,
        )
        self.btn_fill_color._is_color_swatch = True
        self.btn_fill_color.pack(side=tk.LEFT, padx=6)
        tk.Button(
            cf2, text="✖", command=self.clear_fill_color,
            bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
            cursor="hand2", font=("Segoe UI", 8), width=3,
        ).pack(side=tk.LEFT)

        self._style_row_thickness = tk.Frame(sp, bg=self.colors["bg_card"])
        tf = self._style_row_thickness
        tf.pack(fill=tk.X, padx=8, pady=2)
        tk.Label(tf, text="Kalınlık", bg=self.colors["bg_card"], fg=self.colors["text"], font=("Segoe UI", 9)).pack(anchor="w")
        self.thickness_scale = tk.Scale(
            tf, from_=1, to=30, orient=tk.HORIZONTAL, variable=self.thickness,
            bg=self.colors["bg_card"], fg=self.colors["text"], highlightthickness=0,
            troughcolor=self.colors["bg_light"], sliderlength=12, length=200,
        )
        self.thickness_scale.pack(fill=tk.X)

        self._style_row_fontsize = tk.Frame(sp, bg=self.colors["bg_card"])
        ff = self._style_row_fontsize
        ff.pack(fill=tk.X, padx=8, pady=2)
        tk.Label(ff, text="Font boyutu", bg=self.colors["bg_card"], fg=self.colors["text"], font=("Segoe UI", 9)).pack(anchor="w")
        self.font_scale = tk.Scale(
            ff, from_=10, to=150, orient=tk.HORIZONTAL, variable=self.font_size,
            bg=self.colors["bg_card"], fg=self.colors["text"], highlightthickness=0,
            troughcolor=self.colors["bg_light"], sliderlength=12, length=200,
        )
        self.font_scale.pack(fill=tk.X)
        self.text_bg_color = getattr(self, "text_bg_color", "") or ""

        of = tk.Frame(sp, bg=self.colors["bg_card"])
        of.pack(fill=tk.X, padx=8, pady=(2, 8))
        tk.Label(of, text="Şeffaflık", bg=self.colors["bg_card"], fg=self.colors["text"], font=("Segoe UI", 9)).pack(anchor="w")
        self.opacity_scale = tk.Scale(
            of, from_=1, to=100, orient=tk.HORIZONTAL, variable=self.opacity,
            bg=self.colors["bg_card"], fg=self.colors["text"], highlightthickness=0,
            troughcolor=self.colors["bg_light"], sliderlength=12, length=200,
        )
        self.opacity_scale.pack(fill=tk.X)

        self._style_row_actions = tk.Frame(sp, bg=self.colors["bg_card"])
        act = self._style_row_actions
        act.pack(fill=tk.X, padx=8, pady=(4, 8))
        self.btn_style_lock = tk.Button(
            act, text="🔒 Kilitle", command=self.toggle_lock_selected,
            bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
            cursor="hand2", font=("Segoe UI", 8, "bold"),
        )
        self.btn_style_lock.pack(fill=tk.X, pady=2)
        self._attach_tooltip(self.btn_style_lock, "Kilitle / kilidi aç\nKısayol: Ctrl+L")
        tk.Button(
            act, text="📋 Stil kopyala", command=self.copy_style,
            bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
            cursor="hand2", font=("Segoe UI", 8, "bold"),
        ).pack(fill=tk.X, pady=2)
        tk.Button(
            act, text="📥 Stil yapıştır", command=self.paste_style,
            bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
            cursor="hand2", font=("Segoe UI", 8, "bold"),
        ).pack(fill=tk.X, pady=2)
        tk.Button(
            act, text="↺ Stil sıfırla", command=self.reset_style_selected,
            bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
            cursor="hand2", font=("Segoe UI", 8, "bold"),
        ).pack(fill=tk.X, pady=2)

        self._props_bar_visible = False
        self.toolbar_bottom = None  # üst şerit yok; stil sağ panelde

        
        z_btn_style = {"bg": self.colors["bg_light"], "fg": self.colors["text"], "relief": "flat", "cursor": "hand2", "font": ("Segoe UI", 9, "bold"), "activebackground": self.colors["accent"]}
        self._right_sections = {}

        def _mk_right_section(parent, title, key, open_default=True):
            wrap = tk.Frame(parent, bg=self.colors["bg_card"])
            wrap.pack(fill=tk.X, padx=4, pady=(4, 0))
            hdr = tk.Button(
                wrap, text=("▼ " if open_default else "▶ ") + title,
                anchor="w", relief="flat", cursor="hand2",
                bg=self.colors["bg_medium"], fg=self.colors["text"],
                font=("Segoe UI", 10, "bold"), padx=8, pady=6,
            )
            hdr.pack(fill=tk.X)
            body = tk.Frame(wrap, bg=self.colors["bg_card"])
            if open_default:
                body.pack(fill=tk.X, padx=4, pady=4)
            self._right_sections[key] = {"body": body, "hdr": hdr, "open": open_default, "title": title}

            def toggle(k=key):
                info = self._right_sections[k]
                if info["open"]:
                    info["body"].pack_forget()
                    info["hdr"].config(text="▶ " + info["title"])
                    info["open"] = False
                else:
                    info["body"].pack(fill=tk.X, padx=4, pady=4)
                    info["hdr"].config(text="▼ " + info["title"])
                    info["open"] = True
            hdr.config(command=toggle)
            return body

        # —— Katmanlar (kısa liste + scroll) ——
        layer_body = _mk_right_section(right_panel, "📑 Katmanlar", "layers", True)
        lf = tk.Frame(layer_body, bg=self.colors["bg_card"])
        lf.pack(fill=tk.X)
        self.layer_listbox = tk.Listbox(
            lf, bg=self.colors["bg_light"], fg=self.colors["text"],
            selectbackground=self.colors["accent"], font=("Segoe UI", 9),
            height=4, relief="flat", borderwidth=0, exportselection=False,
        )
        lsb = tk.Scrollbar(lf, orient=tk.VERTICAL, command=self.layer_listbox.yview)
        self.layer_listbox.config(yscrollcommand=lsb.set)
        self.layer_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        lsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.layer_listbox.bind("<<ListboxSelect>>", self.on_layer_select)
        self.layer_listbox.bind("<Double-Button-1>", lambda e: self.rename_layer())
        btn_frame = tk.Frame(layer_body, bg=self.colors["bg_card"])
        btn_frame.pack(fill=tk.X, pady=(4, 0))
        tk.Button(btn_frame, text="👁", command=self.toggle_layer_visibility, **z_btn_style, width=3).pack(side=tk.LEFT, padx=1)
        tk.Button(btn_frame, text="✏️", command=self.rename_layer, **z_btn_style, width=3).pack(side=tk.LEFT, padx=1)
        tk.Button(btn_frame, text="➕", command=self.add_layer, **z_btn_style, width=3).pack(side=tk.LEFT, padx=1)
        tk.Button(btn_frame, text="🗑", command=self.delete_selected_object, bg=self.colors["accent"], fg="white", relief="flat", cursor="hand2", font=("Segoe UI", 9, "bold"), width=3).pack(side=tk.LEFT, padx=1)

        # —— Gruplar ——
        group_body = _mk_right_section(right_panel, "🧩 Gruplar", "groups", True)
        gf0 = tk.Frame(group_body, bg=self.colors["bg_card"])
        gf0.pack(fill=tk.X)
        self.group_listbox = tk.Listbox(
            gf0, bg=self.colors["bg_light"], fg=self.colors["text"],
            selectbackground=self.colors["accent"], font=("Segoe UI", 9),
            height=3, relief="flat", borderwidth=0, exportselection=False,
        )
        gsb = tk.Scrollbar(gf0, orient=tk.VERTICAL, command=self.group_listbox.yview)
        self.group_listbox.config(yscrollcommand=gsb.set)
        self.group_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        gsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.group_listbox.bind("<<ListboxSelect>>", self.on_group_select)
        self.group_listbox.bind("<Double-Button-1>", lambda e: self.rename_group())
        gf = tk.Frame(group_body, bg=self.colors["bg_card"])
        gf.pack(fill=tk.X, pady=(4, 0))
        tk.Button(gf, text="🔗 Grupla", command=self.group_selected, **z_btn_style).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=1)
        tk.Button(gf, text="⛓ Çöz", command=self.ungroup_selected, **z_btn_style).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=1)
        gf2 = tk.Frame(group_body, bg=self.colors["bg_card"])
        gf2.pack(fill=tk.X, pady=(2, 0))
        tk.Button(gf2, text="✏️ Grup Adı", command=self.rename_group, **z_btn_style).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=1)

        canvas_frame = tk.Frame(main_container, bg=self.colors["bg_dark"])
        self.canvas_frame = canvas_frame
        canvas_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=4, pady=4)
        
        self.canvas = tk.Canvas(
            canvas_frame, bg=self.colors.get("canvas", "#0d1117"),
            cursor="cross", highlightthickness=1,
            highlightbackground=self.colors.get("border", "#30363d"),
            relief="flat",
            takefocus=1,
        )
        self.canvas.pack(fill=tk.BOTH, expand=True)

        # Köşe araç göstergesi (kırmızı, animasyonlu)
        self.tool_badge = tk.Label(
            self.canvas,
            text="✋ SEÇ",
            fg="#ff2d55",
            bg="#0d1117",
            font=("Segoe UI", 12, "bold"),
            padx=10, pady=6,
            relief="flat",
            bd=0,
        )
        self.tool_badge.place(relx=1.0, rely=0.0, x=-14, y=12, anchor="ne")
        self._badge_pulse_on = True
        self._badge_pulse_job = None
        self.root.after(200, self._pulse_tool_badge)

        self.canvas.bind("<ButtonPress-1>", self.on_press)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<Motion>", self.on_motion)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        self.canvas.bind("<Double-Button-1>", self.on_double_click)
        self.canvas.bind("<ButtonPress-3>", self.start_pan)
        self.canvas.bind("<B3-Motion>", self.do_pan)
        self.canvas.bind("<ButtonRelease-3>", self.end_pan)
        self.canvas.bind("<MouseWheel>", self._on_mousewheel)
        # Linux
        self.canvas.bind("<Button-4>", lambda e: self.zoom(1.08, focus_x=e.x, focus_y=e.y))
        self.canvas.bind("<Button-5>", lambda e: self.zoom(1 / 1.08, focus_x=e.x, focus_y=e.y))
        
        self.root.bind("<Delete>", lambda e: self.delete_selected_object())
        self.root.bind("<BackSpace>", lambda e: self.delete_selected_object())
        self.root.bind("<Control-c>", self.copy_object)
        self.root.bind("<Control-v>", self.paste_object)
        self.root.bind("<Return>", lambda e: self._on_return_key(e))
        self.root.bind("<Escape>", lambda e: self._on_escape_key(e))

        self._bind_shortcuts()

        self.update_layer_ui()
        
        self.status_bar = tk.Frame(main_container, bg=self.colors["bg_medium"], height=28)
        self.status_bar.pack(fill=tk.X, side=tk.BOTTOM)
        self.status_bar.pack_propagate(False)
        self.status_label = tk.Label(
            self.status_bar,
            text="✨ Hazır — tema: 🌙 Karanlık · araç seçerek başla",
            bg=self.colors["bg_medium"], fg=self.colors["success"],
            font=("Segoe UI", 9, "bold"), anchor="w",
        )
        self.status_label.pack(side=tk.LEFT, padx=12, pady=2)


    def _bind_shortcuts(self):
        """Tüm klavye kısayolları — bind_all: canvas odaktayken de çalışır."""
        def _ctrl(e):
            return bool(e.state & 0x4)

        def _safe(fn):
            def _h(e):
                if getattr(self, "_text_entry", None):
                    return
                try:
                    fn()
                except Exception:
                    pass
                return "break"
            return _h

        # Dosya / düzen — global
        ba = self.root.bind_all
        ba("<Control-o>", _safe(self.open_image))
        ba("<Control-s>", _safe(self.save_image))
        ba("<Control-S>", _safe(self.save_project))
        ba("<Control-O>", _safe(self.open_project))
        ba("<Control-n>", _safe(self.new_page))
        ba("<Control-N>", _safe(self.new_page))
        ba("<Control-i>", _safe(self.add_image_object))
        ba("<Control-z>", _safe(self.undo))
        ba("<Control-y>", _safe(self.redo))
        ba("<Control-Z>", _safe(self.redo))
        ba("<Control-a>", _safe(self._select_all))
        ba("<Control-g>", _safe(self.group_selected))
        ba("<Control-G>", _safe(self.ungroup_selected))
        ba("<Control-0>", _safe(self.focus_view))
        ba("<Control-1>", _safe(self.reset_view))
        ba("<Control-plus>", _safe(lambda: self.zoom(1.15)))
        ba("<Control-equal>", _safe(lambda: self.zoom(1.15)))
        ba("<Control-minus>", _safe(lambda: self.zoom(1 / 1.15)))
        ba("<F1>", _safe(self.show_shortcuts_help))
        ba("<Control-h>", _safe(lambda: self.mirror_selected("h")))
        ba("<Control-j>", _safe(lambda: self.mirror_selected("v")))
        ba("<Control-t>", _safe(self.toggle_theme))
        ba("<bracketleft>", _safe(lambda: self.rotate_selected(-15)))
        ba("<bracketright>", _safe(lambda: self.rotate_selected(15)))
        ba("<Control-bracketleft>", _safe(lambda: self.rotate_selected(-90)))
        ba("<Control-bracketright>", _safe(lambda: self.rotate_selected(90)))
        ba("<Control-r>", _safe(lambda: self.rotate_selected(90)))
        ba("<Control-R>", _safe(lambda: self.rotate_selected(90)))
        ba("<Control-Shift-R>", _safe(lambda: self.rotate_selected(-90)))
        ba("<Control-Shift-r>", _safe(lambda: self.rotate_selected(-90)))

        # Tek tuş araçlar — her harf için açık bağlama (en güvenilir)
        self._tool_key_map = {
            "v": "move", "h": "move",
            "b": "pen",
            "r": "rect",
            "u": "square",
            "o": "circle",
            "t": "triangle",
            "p": "hexagon",
            "w": "star",
            "l": "callout",
            "c": "curve",
            "a": "arrow",
            "q": "arrow_path",
            "x": "text",
            "f": "fill",
            "g": "fill",
            "i": "eyedropper",
            "k": "crop",
            "z": "zoom_region",
            "m": "callout",
        }

        def _make_tool_handler(tool_name):
            def _handler(event=None):
                # metin girişi açıkken harfleri ASLA yutma
                if getattr(self, "_text_entry", None):
                    return None
                try:
                    w = self.root.focus_get()
                    if w is not None and w.winfo_class() in ("Entry", "Text", "TEntry"):
                        return None
                except Exception:
                    pass
                if event is not None and (int(event.state) & 0x4):
                    return None
                self._cancel_in_progress_draw()
                self.set_action(tool_name)
                try:
                    self.canvas.focus_set()
                except Exception:
                    pass
                return "break"
            return _handler

        for letter, tool in self._tool_key_map.items():
            handler = _make_tool_handler(tool)
            # bind_all + root + canvas (üç katman)
            for seq in (f"<Key-{letter}>", f"<Key-{letter.upper()}>"):
                ba(seq, handler)
                self.root.bind(seq, handler)
                self.canvas.bind(seq, handler)

        # Stil kopyala / yapıştır
        ba("<Control-Shift-C>", _safe(self.copy_style))
        ba("<Control-Shift-V>", _safe(self.paste_style))
        def _shot(e=None):
            try:
                self.capture_screenshot_region()
            except Exception as ex:
                try:
                    self.status_label.config(text=f"Screenshot hata: {ex}", fg=self.colors["warning"])
                except Exception:
                    pass
            return "break"
        # F9 — güvenilir uygulama içi kısayol (global değil)
        for seq in ("<F9>", "<Key-F9>", "<KeyPress-F9>"):
            ba(seq, _shot)
            self.root.bind(seq, _shot)
            self.canvas.bind(seq, _shot)
        ba("<Control-l>", _safe(self.toggle_lock_selected))
        ba("<Control-L>", _safe(self.toggle_lock_selected))
        ba("<Control-Shift-L>", _safe(self.unlock_all))
        ba("<Control-Shift-l>", _safe(self.unlock_all))
        def _edit_sel_text(e=None):
            o = self.selected_obj
            if o and o.get("type") in ("text", "textbox"):
                self.edit_text_object(o)
                return "break"
        ba("<F2>", _edit_sel_text)
        self.root.bind("<F2>", _edit_sel_text)
        self.canvas.bind("<F2>", _edit_sel_text)
        for key, d in (("Left", "Left"), ("Right", "Right"), ("Up", "Up"), ("Down", "Down")):
            def _mk(dir_=d):
                return lambda e: self._on_arrow_key(e, dir_)
            h = _mk()
            ba(f"<{key}>", h)
            self.root.bind(f"<{key}>", h)
            self.canvas.bind(f"<{key}>", h)
        def _nudge_reset(e=None):
            self._nudge_saved = False
            self._nudge_count = 0
            try:
                self._clear_guides()
            except Exception:
                pass
        for key in ("Left", "Right", "Up", "Down"):
            ba(f"<KeyRelease-{key}>", _nudge_reset)
        self.root.bind("<Control-Shift-C>", _safe(self.copy_style))
        self.root.bind("<Control-Shift-V>", _safe(self.paste_style))

        self.canvas.bind("<ButtonPress-1>", lambda e: self.canvas.focus_set(), add="+")
        self.canvas.bind("<Enter>", lambda e: self.canvas.focus_set(), add="+")
        self.root.after(100, lambda: self.canvas.focus_set())


    def copy_style(self):
        """Seçili nesnenin stilini panoya al. Metinde yalnızca renk."""
        o = self.selected_obj
        if not o:
            self.status_label.config(text="Stil kopyalamak için nesne seç", fg=self.colors["warning"])
            return
        t = o.get("type")
        if t in ("text", "textbox"):
            col = o.get("color") or self.outline_color
            self.style_clipboard = {
                "mode": "text_color",
                "color": col,
            }
            self.status_label.config(
                text=f"📋 Metin rengi kopyalandı: {col}",
                fg=self.colors["success"],
            )
            return
        self.style_clipboard = {
            "mode": "full",
            "color": o.get("color"),
            "fill": o.get("fill", ""),
            "width": o.get("width"),
            "opacity": o.get("opacity", 100),
            "size": o.get("size"),
            "label_size": o.get("label_size"),
            "label_color": o.get("label_color"),
        }
        self.status_label.config(
            text="📋 Stil kopyalandı (Ctrl+Shift+V ile yapıştır)",
            fg=self.colors["success"],
        )

    def reset_style_selected(self):
        """Seçili nesne(ler)i varsayılan stil ayarlarına döndür."""
        targets = list(self.selected_objs) if self.selected_objs else (
            [self.selected_obj] if self.selected_obj else []
        )
        targets = [o for o in targets if o and o in self.objects and not self._is_locked(o)]
        if not targets:
            self.status_label.config(text="Stil sıfırlamak için nesne seç", fg=self.colors["warning"])
            return
        self.save_state()
        for o in targets:
            t = o.get("type")
            o["color"] = self._default_outline
            o["opacity"] = self._default_opacity
            if t in ("text", "textbox"):
                o["size"] = self._default_font_size
                o["bg_color"] = ""
            else:
                o["width"] = self._default_thickness
                o["fill"] = self._default_fill or ""
                if "label" in o or o.get("label_color"):
                    o["label_color"] = self._default_outline
                    o["label_size"] = self._default_font_size
        self.outline_color = self._default_outline
        self.fill_color = self._default_fill or ""
        self._suspend_prop_trace = True
        try:
            self.thickness.set(self._default_thickness)
            self.font_size.set(self._default_font_size)
            self.opacity.set(self._default_opacity)
        finally:
            self._suspend_prop_trace = False
        try:
            if getattr(self, "btn_outline_color", None):
                self.btn_outline_color.config(bg=self._default_outline, activebackground=self._default_outline)
            if getattr(self, "btn_font_color", None):
                self.btn_font_color.config(bg=self._default_outline, activebackground=self._default_outline)
            if getattr(self, "btn_fill_color", None):
                if self._default_fill:
                    self.btn_fill_color.config(bg=self._default_fill, text="Renk")
                else:
                    self.btn_fill_color.config(bg="gray", text="Yok")
        except Exception:
            pass
        self.invalidate_cache()
        self.redraw()
        self.status_label.config(text="↺ Stil varsayılana döndü", fg=self.colors["success"])

    def paste_style(self):

        """Kopyalanan stili seçili nesnelere uygula."""
        st = self.style_clipboard
        if not st:
            self.status_label.config(text="Önce stil kopyala (Ctrl+Shift+C)", fg=self.colors["warning"])
            return
        targets = list(self.selected_objs) if self.selected_objs else (
            [self.selected_obj] if self.selected_obj else []
        )
        targets = [o for o in targets if o in self.objects]
        if not targets:
            self.status_label.config(text="Yapıştırmak için nesne seç", fg=self.colors["warning"])
            return
        self.save_state()
        # yalnızca metin rengi kopyası
        if st.get("mode") == "text_color":
            col = st.get("color")
            if not col:
                return
            for o in targets:
                t = o.get("type")
                if t in ("text", "textbox"):
                    o["color"] = col
                elif t not in ("image", "fill_region"):
                    o["label_color"] = col
            try:
                if getattr(self, "btn_font_color", None):
                    self.btn_font_color.config(bg=col, activebackground=col)
            except Exception:
                pass
            self.invalidate_cache()
            self.redraw()
            self.status_label.config(text=f"📥 Yazı rengi yapıştırıldı: {col}", fg=self.colors["success"])
            return
        for o in targets:
            t = o.get("type")
            if st.get("color") and t != "image":
                o["color"] = st["color"]
            if t not in ("text", "pen", "arrow", "curve", "image", "fill_region"):
                if "fill" in st:
                    o["fill"] = st["fill"] or ""
            if st.get("width") is not None and t not in ("text", "image", "fill_region"):
                o["width"] = st["width"]
            if st.get("opacity") is not None:
                o["opacity"] = st["opacity"]
            if t in ("text", "textbox") and st.get("size") is not None:
                o["size"] = st["size"]
            if o.get("label") is not None:
                if st.get("label_size") is not None:
                    o["label_size"] = st["label_size"]
                elif st.get("size") is not None:
                    o["label_size"] = st["size"]
                if st.get("label_color"):
                    o["label_color"] = st["label_color"]
                elif st.get("color"):
                    o["label_color"] = st["color"]
            o.pop("_rz_cache", None)
        self.invalidate_cache()
        self.redraw()
        self.status_label.config(text=f"📋 Stil yapıştırıldı ({len(targets)} nesne)", fg=self.colors["success"])

    def _cancel_in_progress_draw(self):
        """Yarım kalan çizim / sürüklemeyi temizle."""
        for o in getattr(self, "objects", []) or []:
            o.pop("_drag_hide", None)
        self.current_pen_obj = None
        for item in getattr(self, "temp_items", []) or []:
            try:
                self.canvas.delete(item)
            except Exception:
                pass
        self.temp_items = []
        for item in getattr(self, "drag_items", []) or []:
            try:
                self.canvas.delete(item)
            except Exception:
                pass
        self.drag_items = []
        self.start_x = None
        self.start_y = None
        self._multi_drag = False
        self.resize_handle = None
        self._marquee = None
        try:
            self.canvas.delete("marquee")
            self.canvas.delete("temp_preview")
            self.canvas.delete("drag_preview")
        except Exception:
            pass

    def _pulse_tool_badge(self):
        """Kırmızı araç rozeti nabız animasyonu."""
        if not getattr(self, "tool_badge", None):
            return
        try:
            if not self.tool_badge.winfo_exists():
                return
        except Exception:
            return
        on = getattr(self, "_badge_pulse_on", True)
        try:
            if on:
                self.tool_badge.config(fg="#ff2d55")
            else:
                self.tool_badge.config(fg="#ff8fa3")
        except Exception:
            return
        self._badge_pulse_on = not on
        self._badge_pulse_job = self.root.after(450, self._pulse_tool_badge)

    def _update_tool_badge(self, action):
        labels = {
            "move": "✋ SEÇ",
            "pen": "🖊 FIRÇA",
            "rect": "⬜ DİKDÖRTGEN",
            "square": "⬛ KARE",
            "circle": "⭕ DAİRE",
            "hexagon": "⬡ ALTIĞEN",
            "star": "⭐ YILDIZ",
            "callout": "💬 CALLOUT",
            "triangle": "🔺 ÜÇGEN",
            "curve": "〰 EĞRİ",
            "arrow": "↗ OK",
            "arrow_path": "↩ OK YOL",
            "text": "🔤 METİN",
            "fill": "🪣 DOLDUR",
            "eyedropper": "💧 RENK AL",
            "crop": "✂ KIRP",
            "zoom_region": "🔍 BÖLGE ZOOM",
        }
        txt = labels.get(action, str(action).upper())
        if getattr(self, "tool_badge", None):
            try:
                self.tool_badge.config(text=txt, fg="#ff2d55")
                self.tool_badge.lift()
            except Exception:
                pass

    def _select_all(self):
        visible = {L["id"] for L in self.layers if L.get("visible")}
        objs = [o for o in self.objects if o.get("layer", 0) in visible]
        if not objs:
            return
        self.selected_objs = list(objs)
        self.selected_obj = objs[-1] if objs else None
        self.redraw()
        self.status_label.config(text=f"Tümü seçildi ({len(objs)})", fg=self.colors["success"])


    def show_project_menu(self):
        """Üst Proje menüsü."""
        menu = tk.Menu(
            self.root, tearoff=0,
            bg=self.colors["bg_medium"], fg=self.colors["text"],
            activebackground=self.colors["accent"], activeforeground="white",
            font=("Segoe UI", 10),
        )
        menu.add_command(label="📂 Resim Aç", command=self.open_image)
        menu.add_command(label="📂 Proje Aç", command=self.open_project)
        menu.add_command(label="💾 Resim Kaydet", command=self.save_image)
        menu.add_command(label="💾 Proje Kaydet", command=self.save_project)
        menu.add_separator()
        menu.add_command(label="🆕 Yeni Sayfa", command=self.new_page)
        menu.add_command(label="🖼 Resim Ekle", command=self.add_image_object)
        menu.add_command(label="↔ Sayfa Boyutu", command=self.start_page_resize)
        try:
            menu.tk_popup(
                self.btn_project.winfo_rootx(),
                self.btn_project.winfo_rooty() + self.btn_project.winfo_height(),
            )
        except Exception:
            menu.tk_popup(self.root.winfo_pointerx(), self.root.winfo_pointery())
        finally:
            try:
                menu.grab_release()
            except Exception:
                pass

    def show_quick_tools_menu(self):
        """Hızlı araçlar: döndür, katman sırası, ayna, sığdır."""
        menu = tk.Menu(
            self.root, tearoff=0,
            bg=self.colors["bg_medium"], fg=self.colors["text"],
            activebackground=self.colors["accent"], activeforeground="white",
            font=("Segoe UI", 10),
        )
        rot = tk.Menu(
            menu, tearoff=0,
            bg=self.colors["bg_medium"], fg=self.colors["text"],
            activebackground=self.colors["accent"], activeforeground="white",
            font=("Segoe UI", 10),
        )
        rot.add_command(label="↺ 15° sola", command=lambda: self.rotate_selected(-15))
        rot.add_command(label="↻ 15° sağa", command=lambda: self.rotate_selected(15))
        rot.add_separator()
        rot.add_command(label="↺ 90° sola", command=lambda: self.rotate_selected(-90))
        rot.add_command(label="↻ 90° sağa", command=lambda: self.rotate_selected(90))
        menu.add_cascade(label="🔄 Döndür", menu=rot)

        lay = tk.Menu(
            menu, tearoff=0,
            bg=self.colors["bg_medium"], fg=self.colors["text"],
            activebackground=self.colors["accent"], activeforeground="white",
            font=("Segoe UI", 10),
        )
        lay.add_command(label="⬆ Yukarı getir", command=self.bring_forward)
        lay.add_command(label="⬇ Aşağı getir", command=self.send_backward)
        lay.add_command(label="⇞ En öne", command=self.bring_to_front)
        lay.add_command(label="⇟ En arkaya", command=self.send_to_back)
        menu.add_cascade(label="📑 Katman sırası", menu=lay)

        menu.add_separator()
        menu.add_command(label="↔ Yatay ayna", command=lambda: self.mirror_selected("h"))
        menu.add_command(label="↕ Dikey ayna", command=lambda: self.mirror_selected("v"))
        menu.add_separator()
        menu.add_command(label="🔓 Tüm kilitleri kaldır", command=self.unlock_all)
        menu.add_command(label="🎯 Sığdır", command=self.focus_view)
        try:
            menu.tk_popup(
                self.btn_quick.winfo_rootx(),
                self.btn_quick.winfo_rooty() + self.btn_quick.winfo_height(),
            )
        except Exception:
            menu.tk_popup(self.root.winfo_pointerx(), self.root.winfo_pointery())
        finally:
            try:
                menu.grab_release()
            except Exception:
                pass

    def show_settings_menu(self):
        """Sol üst ayarlar: tema, snap rengi, lisans."""
        menu = tk.Menu(self.root, tearoff=0, bg=self.colors["bg_medium"], fg=self.colors["text"],
                       activebackground=self.colors["accent"], activeforeground="white",
                       font=("Segoe UI", 10))
        theme_label = "🌙 Karanlık temaya geç" if self.theme_name == "light" else "☀️ Açık temaya geç"
        menu.add_command(label=theme_label, command=self.toggle_theme)
        menu.add_command(label="🎯 Snap çizgi rengi…", command=self.choose_snap_color)
        menu.add_separator()
        menu.add_command(label="© Lisans / İletişim", command=self.show_license)
        try:
            menu.tk_popup(self.btn_settings.winfo_rootx(), self.btn_settings.winfo_rooty() + self.btn_settings.winfo_height())
        except Exception:
            menu.tk_popup(self.root.winfo_pointerx(), self.root.winfo_pointery())
        finally:
            try:
                menu.grab_release()
            except Exception:
                pass

    def show_license(self):
        win = tk.Toplevel(self.root)
        win.title("Lisans")
        win.configure(bg=self.colors["bg_medium"])
        win.resizable(False, False)
        win.transient(self.root)
        frm = tk.Frame(win, bg=self.colors["bg_medium"], padx=20, pady=16)
        frm.pack(fill=tk.BOTH, expand=True)
        tk.Label(
            frm, text="Ultimate Image Editor",
            bg=self.colors["bg_medium"], fg=self.colors["accent"],
            font=("Segoe UI", 14, "bold"),
        ).pack(anchor="w")
        tk.Label(
            frm,
            text="Okan KOÇER tarafından yapılmıştır.",
            bg=self.colors["bg_medium"], fg=self.colors["text"],
            font=("Segoe UI", 11),
        ).pack(anchor="w", pady=(10, 2))
        tk.Label(
            frm,
            text="© Tüm hakları saklıdır. / All rights reserved.",
            bg=self.colors["bg_medium"], fg=self.colors["text_secondary"],
            font=("Segoe UI", 9),
        ).pack(anchor="w", pady=(0, 8))
        tk.Label(
            frm, text="MIT Lisansı",
            bg=self.colors["bg_medium"], fg=self.colors["accent"],
            font=("Segoe UI", 10, "bold"),
        ).pack(anchor="w", pady=(4, 2))
        mit = (
            "Permission is hereby granted, free of charge, to any person obtaining a copy "
            "of this software and associated documentation files (the \"Software\"), to deal "
            "in the Software without restriction, including without limitation the rights "
            "to use, copy, modify, merge, publish, distribute, sublicense, and/or sell "
            "copies of the Software, and to permit persons to whom the Software is "
            "furnished to do so, subject to the following conditions:\n\n"
            "The above copyright notice and this permission notice shall be included in "
            "all copies or substantial portions of the Software.\n\n"
            "THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR "
            "IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, "
            "FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT."
        )
        txt = tk.Text(
            frm, wrap=tk.WORD, height=10, width=56,
            bg=self.colors["bg_light"], fg=self.colors["text"],
            font=("Segoe UI", 8), relief="flat", padx=8, pady=8,
        )
        txt.pack(fill=tk.BOTH, expand=True, pady=4)
        txt.insert("1.0", mit)
        txt.configure(state="disabled")
        tk.Label(
            frm,
            text="İletişim: okankocer@outlook.com",
            bg=self.colors["bg_medium"], fg=self.colors["text"],
            font=("Segoe UI", 10, "bold"),
        ).pack(anchor="w", pady=(10, 4))
        tk.Button(
            frm, text="Kapat", command=win.destroy,
            bg=self.colors["accent"], fg="white", relief="flat",
            font=("Segoe UI", 9, "bold"), padx=16, pady=4, cursor="hand2",
        ).pack(anchor="e", pady=(8, 0))
        win.update_idletasks()
        try:
            x = self.root.winfo_rootx() + 80
            y = self.root.winfo_rooty() + 80
            win.geometry(f"+{x}+{y}")
        except Exception:
            pass

    def show_shortcuts_help(self):
        """Uygulama içi kısayol listesi."""
        win = tk.Toplevel(self.root)
        win.title("⌨ Klavye Kısayolları")
        win.geometry("520x640")
        win.configure(bg=self.colors["bg_medium"])
        win.transient(self.root)
        frm = tk.Frame(win, bg=self.colors["bg_medium"])
        frm.pack(fill=tk.BOTH, expand=True, padx=12, pady=12)
        tk.Label(
            frm, text="⌨ Klavye Kısayolları",
            bg=self.colors["bg_medium"], fg=self.colors["accent"],
            font=("Segoe UI", 14, "bold"),
        ).pack(anchor="w", pady=(0, 8))
        text = tk.Text(
            frm, wrap=tk.WORD, font=("Consolas", 10),
            bg=self.colors["bg_light"], fg=self.colors["text"],
            relief="flat", padx=12, pady=10, height=32,
        )
        text.pack(fill=tk.BOTH, expand=True)
        help_txt = """DOSYA\nCtrl+O          Resim Aç\nCtrl+Shift+O    Proje Aç\nCtrl+S          Resim Kaydet\nCtrl+Shift+S    Proje Kaydet\nCtrl+N          Yeni Sayfa\nCtrl+I          Resim Ekle\nF9              Ekran görüntüsü\n\nDÜZENLEME\nCtrl+Z          Geri Al\nCtrl+Y          İleri Al\nCtrl+C / Ctrl+V Kopyala / Yapıştır\nDelete          Seçileni sil\nCtrl+A          Tümünü seç\nCtrl+G          Grupla\nCtrl+Shift+G    Grubu çöz\nCtrl+L          Kilitle / kilidi aç\nCtrl+Shift+L    Tüm kilitleri aç\nF2              Seçili metni düzenle\nOk tuşları      Seçiliyi taşı (basılı tut = hızlan)\n\nARAÇLAR\nV / H           Seç / Taşı\nB               Fırça\nR               Dikdörtgen\nU               Kare\nT               Üçgen\nP               Altıgen\nW               Yıldız\nL               Callout\nC               Eğri\nA               Ok\nQ               Ok yolu (waypoint)\nX               Metin\nG / F           Doldur (kova)\nI               Renk Al\nK               Kırp\nZ               Bölge Zoom\n\nGÖRÜNÜM\nCtrl+0          Sığdır\nCtrl+1          1:1 Orijinal\nCtrl++ / Ctrl+- Yakınlaştır / Uzaklaştır\nCtrl+T          Tema değiştir\nF1              Bu yardım\n\nSTİL\nCtrl+Shift+C    Stil kopyala\nCtrl+Shift+V    Stili yapıştır\n\nDÖNÜŞTÜR\n[ / ]           15° sola / sağa\nCtrl+[ / ]      90° sola / sağa\nCtrl+R          90° sağa (rotate)\nCtrl+Shift+R    90° sola\nCtrl+H          Yatay ayna\nCtrl+J          Dikey ayna\n\nMETİN\nEnter           Onayla\nCtrl+Enter      Yeni satır\nEsc             İptal\n← → ↑ ↓         İmleç (düzenlerken)\n\nDİĞER\nSağ tık         Kaydır / Seç\nÇift sağ tık    Özellikler\nÇift sol tık    Metin düzenle / şekil metni\nShift (çizerken) 90° kilit\nEnter / Esc     Kırp uygula / iptal\n"""

        text.insert("1.0", help_txt)
        text.config(state=tk.DISABLED)
        tk.Button(
            frm, text="Kapat", command=win.destroy,
            bg=self.colors["accent"], fg="white", relief="flat",
            font=("Segoe UI", 10, "bold"), padx=16, pady=6, cursor="hand2",
        ).pack(pady=(10, 0))

    def new_page(self):
        """Boyutu seçilebilir beyaz yeni sayfa"""
        dialog = tk.Toplevel(self.root)
        dialog.title("🆕 Yeni Sayfa")
        dialog.configure(bg=self.colors["bg_medium"])
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()

        tk.Label(dialog, text="Sayfa Boyutları (piksel)", bg=self.colors["bg_medium"],
                 fg=self.colors["text"], font=("Segoe UI", 11, "bold")).pack(pady=(15, 8))

        form = tk.Frame(dialog, bg=self.colors["bg_medium"])
        form.pack(padx=20, pady=5)

        tk.Label(form, text="Genişlik:", bg=self.colors["bg_medium"], fg=self.colors["text"],
                 font=("Segoe UI", 10)).grid(row=0, column=0, sticky="e", padx=5, pady=5)
        w_var = tk.StringVar(value="800")
        tk.Entry(form, textvariable=w_var, width=10, font=("Segoe UI", 11)).grid(row=0, column=1, padx=5, pady=5)

        tk.Label(form, text="Yükseklik:", bg=self.colors["bg_medium"], fg=self.colors["text"],
                 font=("Segoe UI", 10)).grid(row=1, column=0, sticky="e", padx=5, pady=5)
        h_var = tk.StringVar(value="600")
        tk.Entry(form, textvariable=h_var, width=10, font=("Segoe UI", 11)).grid(row=1, column=1, padx=5, pady=5)

        presets = tk.Frame(dialog, bg=self.colors["bg_medium"])
        presets.pack(pady=8)

        def apply_preset(pw, ph):
            w_var.set(str(pw))
            h_var.set(str(ph))

        for label, pw, ph in [("A4 150dpi", 1240, 1754), ("HD", 1280, 720), ("Kare", 1000, 1000), ("800x600", 800, 600)]:
            tk.Button(presets, text=label, command=lambda a=pw, b=ph: apply_preset(a, b),
                      bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
                      font=("Segoe UI", 9), padx=8, pady=4, cursor="hand2").pack(side=tk.LEFT, padx=3)

        result = {"ok": False}

        def confirm():
            try:
                w = int(w_var.get().strip())
                h = int(h_var.get().strip())
                if w < 50 or h < 50 or w > 10000 or h > 10000:
                    messagebox.showwarning("Uyarı", "Boyut 50–10000 arasında olmalı", parent=dialog)
                    return
                result["ok"] = True
                result["w"] = w
                result["h"] = h
                dialog.destroy()
            except ValueError:
                messagebox.showwarning("Uyarı", "Geçerli sayı girin", parent=dialog)

        def cancel():
            dialog.destroy()

        btn_row = tk.Frame(dialog, bg=self.colors["bg_medium"])
        btn_row.pack(pady=(5, 15))
        tk.Button(btn_row, text="Oluştur", command=confirm, bg=self.colors["accent"], fg="white",
                  relief="flat", font=("Segoe UI", 10, "bold"), padx=16, pady=6, cursor="hand2").pack(side=tk.LEFT, padx=6)
        tk.Button(btn_row, text="İptal", command=cancel, bg=self.colors["bg_light"], fg=self.colors["text"],
                  relief="flat", font=("Segoe UI", 10), padx=16, pady=6, cursor="hand2").pack(side=tk.LEFT, padx=6)

        dialog.update_idletasks()
        x = self.root.winfo_rootx() + (self.root.winfo_width() - dialog.winfo_width()) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - dialog.winfo_height()) // 2
        dialog.geometry(f"+{x}+{y}")
        self.root.wait_window(dialog)

        if not result.get("ok"):
            return

        self.save_state()
        self.original_image = Image.new("RGBA", (result["w"], result["h"]), (255, 255, 255, 255))
        self.objects = []
        self.selected_obj = None
        self.history = []
        self.redo_stack = []
        self.invalidate_cache()
        self.scale = 1.0
        self.pan_x = 0
        self.pan_y = 0
        self.drag_items = []
        self.temp_items = []
        self.canvas.delete("all")

        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw > 1 and ch > 1:
            self.scale = min((cw - 40) / result["w"], (ch - 40) / result["h"], 1.0)
        self._initial_scale = self.scale

        self.dirty = False
        self.project_path = None
        self.redraw()
        self.status_label.config(
            text=f"🆕 Yeni beyaz sayfa: {result['w']}×{result['h']}",
            fg=self.colors["success"]
        )

    def add_image_object(self):
        """Sayfaya bir veya birden fazla resim nesnesi ekle (boyutlandırılabilir)"""
        filepaths = filedialog.askopenfilenames(
            title="Resim Ekle",
            filetypes=[
                ("Resimler", "*.png *.jpg *.jpeg *.bmp *.gif *.webp *.tiff"),
                ("Tümü", "*.*")
            ]
        )
        if not filepaths:
            return

        self.save_state()
        page_w, page_h = self.original_image.size
        offset = 20

        for fp in filepaths:
            try:
                img = Image.open(fp).convert("RGBA")
            except Exception as e:
                messagebox.showerror("Hata", f"Açılamadı:\n{fp}\n{e}")
                continue

            iw, ih = img.size
            # Sayfaya sığdır (max %70), oranı koru
            max_w, max_h = page_w * 0.7, page_h * 0.7
            ratio = min(max_w / iw, max_h / ih, 1.0)
            dw, dh = max(1, int(iw * ratio)), max(1, int(ih * ratio))

            x1 = min(offset, max(0, page_w - dw - 10))
            y1 = min(offset, max(0, page_h - dh - 10))

            self.objects.append({
                'type': 'image',
                'layer': self.current_layer_id,
                'x1': float(x1),
                'y1': float(y1),
                'x2': float(x1 + dw),
                'y2': float(y1 + dh),
                'pil_image': img,
                'color': self.outline_color,
                'opacity': self.opacity.get(),
                'name': fp.replace("\\", "/").split("/")[-1]
            })
            offset += 30

        self.selected_obj = self.objects[-1] if self.objects else None
        self.redraw()
        self.status_label.config(
            text=f"🖼 {len(filepaths)} resim eklendi — kırpmak için Kırp aracı veya özellikler",
            fg=self.colors["success"],
        )


    def _clone_objects(self, objects):
        """PIL Image içeren nesneleri güvenli kopyala"""
        cloned = []
        for obj in objects:
            o = {k: v for k, v in obj.items() if k not in ('id', '_rz_cache')}
            if 'pil_image' in o and o['pil_image'] is not None:
                o['pil_image'] = o['pil_image'].copy()
            if 'points' in o:
                o['points'] = list(o['points'])
            cloned.append(o)
        return cloned

    def save_state(self):
        """İçerik snapshot — zoom/pan geri alınmaz; sadece sayfa/nesne."""
        if not self.original_image:
            return
        # Büyük resimde UI donmasın diye history kısa tutulur
        try:
            self.history.append({
                'image': self.original_image.copy(),
                'objects': self._clone_objects(self.objects),
                'layers': copy.deepcopy(self.layers),
                'scale': self.scale,
                'pan_x': self.pan_x,
                'pan_y': self.pan_y,
                'initial_scale': getattr(self, '_initial_scale', self.scale),
            })
        except Exception:
            return
        # Sonsuz history büyük resimlerde RAM doldurur; 40 adım güvenli üst sınır
        while len(self.history) > 40:
            self.history.pop(0)
        self.redo_stack = []  # yeni işlem → ileri al sıfırlanır
        self.dirty = True

    def _snapshot_now(self):
        """Mevcut içeriğin kopyası (undo/redo için)."""
        if not self.original_image:
            return None
        return {
            'image': self.original_image.copy(),
            'objects': self._clone_objects(self.objects),
            'layers': copy.deepcopy(self.layers),
            'scale': self.scale,
            'pan_x': self.pan_x,
            'pan_y': self.pan_y,
            'initial_scale': getattr(self, '_initial_scale', self.scale),
        }

    def _apply_state(self, state):
        self.original_image = state['image']
        self.objects = state['objects']
        self.layers = state['layers']
        self.selected_obj = None
        self.scale = state.get('scale', self.scale)
        self.pan_x = state.get('pan_x', 0)
        self.pan_y = state.get('pan_y', 0)
        self._initial_scale = state.get('initial_scale', self.scale)
        self.invalidate_cache()
        self.drag_items = []
        self.temp_items = []
        self._clear_guides()
        self.canvas.delete("pen_stroke")
        self.canvas.delete("drag_preview")
        self.update_layer_ui()

    def undo(self):
        if not self.history:
            self.status_label.config(text="Geri alınacak işlem yok", fg=self.colors["warning"])
            return
        if getattr(self, '_zoom_after_id', None):
            try:
                self.root.after_cancel(self._zoom_after_id)
            except Exception:
                pass
            self._zoom_after_id = None
        self._interaction_mode = False

        cur = self._snapshot_now()
        if cur is not None:
            self.redo_stack.append(cur)
            while len(self.redo_stack) > 40:
                self.redo_stack.pop(0)

        state = self.history.pop()
        self._apply_state(state)
        self.dirty = True
        self.status_label.config(text="↩ Geri alınıyor…", fg=self.colors["warning"])
        self.root.after(10, lambda: self._hist_redraw("↩ Geri alındı"))

    def redo(self):
        if not getattr(self, 'redo_stack', None):
            self.status_label.config(text="İleri alınacak işlem yok", fg=self.colors["warning"])
            return
        if getattr(self, '_zoom_after_id', None):
            try:
                self.root.after_cancel(self._zoom_after_id)
            except Exception:
                pass
            self._zoom_after_id = None
        self._interaction_mode = False

        cur = self._snapshot_now()
        if cur is not None:
            self.history.append(cur)
            while len(self.history) > 40:
                self.history.pop(0)

        state = self.redo_stack.pop()
        self._apply_state(state)
        self.dirty = True
        self.status_label.config(text="↪ İleri alınıyor…", fg=self.colors["warning"])
        self.root.after(10, lambda: self._hist_redraw("↪ İleri alındı"))

    def _hist_redraw(self, msg):
        try:
            self.redraw()
            self.status_label.config(text=msg, fg=self.colors["success"])
        except Exception as e:
            self.status_label.config(text=f"Geçmiş hatası: {e}", fg=self.colors["accent"])

    def _undo_redraw(self):
        self._hist_redraw("↩ Geri alındı")

    def invalidate_cache(self):
        self.cached_bg = None
        self.cached_scale = None
        self._hq_pil = None
        self._hq_scale = None



    def _detect_window_snap_lines(self, img, max_lines=48):
        """Ekran görüntüsünden gerçek kenar çizgilerini bul (yatay/dikey)."""
        g = img.convert("L")
        w, h = g.size
        # hız için örnekleme
        step = max(1, min(w, h) // 800)
        pix = g.load()
        # satır / sütun kenar skoru
        row_score = [0] * h
        col_score = [0] * w
        for y in range(1, h - 1, step):
            s = 0
            for x in range(0, w, step * 2):
                s += abs(pix[x, y] - pix[x, y - 1])
            row_score[y] = s
        for x in range(1, w - 1, step):
            s = 0
            for y in range(0, h, step * 2):
                s += abs(pix[x, y] - pix[x - 1, y])
            col_score[x] = s
        def peaks(scores, axis_len, min_gap=12):
            thr = max(scores) * 0.35 if scores and max(scores) > 0 else 0
            cand = [(i, scores[i]) for i in range(axis_len) if scores[i] >= thr]
            cand.sort(key=lambda t: -t[1])
            picked = []
            for i, scv in cand:
                if all(abs(i - p) >= min_gap for p in picked):
                    picked.append(i)
                if len(picked) >= max_lines // 2:
                    break
            # kenarlar her zaman
            for edge in (0, axis_len - 1):
                if edge not in picked:
                    picked.append(edge)
            return sorted(picked)
        xs = peaks(col_score, w)
        ys = peaks(row_score, h)
        return xs, ys


    def _install_global_screenshot_hotkey(self):
        """Devre dışı — F9 kullan."""
        return
        """Sistem genelinde F9 (Windows RegisterHotKey)."""
        import sys
        if sys.platform != "win32":
            return
        try:
            import ctypes
            from ctypes import wintypes
            import threading
            user32 = ctypes.windll.user32
            MOD_CONTROL, MOD_SHIFT, MOD_NOREPEAT = 0x0002, 0x0004, 0x4000
            VK_X = 0x58
            HOTKEY_ID = 0x71C0  # unique-ish

            def register():
                try:
                    user32.UnregisterHotKey(None, HOTKEY_ID)
                except Exception:
                    pass
                mods = MOD_CONTROL | MOD_SHIFT | MOD_NOREPEAT
                ok = user32.RegisterHotKey(None, HOTKEY_ID, mods, VK_X)
                if not ok:
                    # MOD_NOREPEAT eski Windows'ta yok
                    ok = user32.RegisterHotKey(None, HOTKEY_ID, MOD_CONTROL | MOD_SHIFT, VK_X)
                if not ok:
                    return
                def loop():
                    msg = wintypes.MSG()
                    while getattr(self, "_hotkey_alive", True):
                        try:
                            r = user32.GetMessageW(ctypes.byref(msg), None, 0, 0)
                            if r == 0 or r == -1:
                                break
                            if msg.message == 0x0312 and msg.wParam == HOTKEY_ID:
                                self.root.after(0, self.capture_screenshot_region)
                            user32.TranslateMessage(ctypes.byref(msg))
                            user32.DispatchMessageW(ctypes.byref(msg))
                        except Exception:
                            break
                    try:
                        user32.UnregisterHotKey(None, HOTKEY_ID)
                    except Exception:
                        pass
                self._hotkey_alive = True
                threading.Thread(target=loop, daemon=True, name="ss-hotkey").start()
            self.root.after(800, register)
        except Exception:
            pass

    def capture_screenshot_region(self):
        """Masaüstü bölge seçimi — yalnızca gerçek kenarlara snap."""
        try:
            from PIL import ImageGrab
        except Exception:
            messagebox.showerror("Hata", "ImageGrab kullanılamıyor")
            return

        self.root.withdraw()
        self.root.update()
        time.sleep(0.35)
        try:
            try:
                full = ImageGrab.grab(all_screens=True)
            except TypeError:
                full = ImageGrab.grab()
        except Exception as e:
            self.root.deiconify()
            messagebox.showerror("Hata", f"Ekran alınamadı:\n{e}")
            return

        full = full.convert("RGBA")
        fw, fh = full.size
        snap_xs, snap_ys = self._detect_window_snap_lines(full)

        overlay = tk.Toplevel()
        overlay.attributes("-fullscreen", True)
        overlay.attributes("-topmost", True)
        overlay.configure(bg="black")
        overlay.focus_force()

        max_w, max_h = overlay.winfo_screenwidth(), overlay.winfo_screenheight()
        ratio = min(1.0, max_w / fw, max_h / fh)
        disp = full if ratio >= 0.999 else full.resize(
            (max(1, int(fw * ratio)), max(1, int(fh * ratio))), Image.Resampling.BILINEAR
        )
        photo = ImageTk.PhotoImage(disp)
        cv = tk.Canvas(overlay, highlightthickness=0, cursor="cross", bg="black")
        cv.pack(fill=tk.BOTH, expand=True)
        cv.create_image(0, 0, anchor=tk.NW, image=photo, tags="bg")
        cv.image = photo

        # Kenar çizgileri (sönük) — sadece algılananlar
        for x in snap_xs:
            sx = int(x * ratio)
            cv.create_line(sx, 0, sx, int(fh * ratio), fill="#2a9d8f", dash=(3, 5), width=1, tags="snap")
        for y in snap_ys:
            sy = int(y * ratio)
            cv.create_line(0, sy, int(fw * ratio), sy, fill="#2a9d8f", dash=(3, 5), width=1, tags="snap")


        state = {
            "x1": 0, "y1": 0, "x2": 0, "y2": 0,
            "dragging": False, "ready": False, "handle": None,
            "regions": [],
            "rbtn": False,
            "crop_edit": False,  # C ile açılır — rastgele tık kırpmaz
        }
        thr = 10
        xs_d = sorted(set(int(x * ratio) for x in snap_xs))
        ys_d = sorted(set(int(y * ratio) for y in snap_ys))
        HR = 6

        def snap_val(v, anchors_disp):
            best, bd = v, thr
            for a in anchors_disp:
                if abs(v - a) < bd:
                    best, bd = a, abs(v - a)
            return best

        def norm_box():
            x1, x2 = sorted([state["x1"], state["x2"]])
            y1, y2 = sorted([state["y1"], state["y2"]])
            state["x1"], state["x2"], state["y1"], state["y2"] = x1, x2, y1, y2

        def handles():
            norm_box()
            x1, y1, x2, y2 = state["x1"], state["y1"], state["x2"], state["y2"]
            cx, cy = (x1 + x2) / 2, (y1 + y2) / 2
            return {
                "nw": (x1, y1), "n": (cx, y1), "ne": (x2, y1),
                "e": (x2, cy), "se": (x2, y2), "s": (cx, y2),
                "sw": (x1, y2), "w": (x1, cy),
            }

        def hit_handle(px, py):
            if not state["ready"]:
                return None
            for name, (hx, hy) in handles().items():
                if abs(px - hx) <= HR + 1 and abs(py - hy) <= HR + 1:
                    return name
            return None

        def draw_sel():
            cv.delete("sel")
            cv.delete("hnd")
            if not state["ready"] and not state["dragging"]:
                cv.delete("hint")
                cv.create_text(
                    12, 12, anchor="nw", fill="white", tags="hint",
                    font=("Segoe UI", 11, "bold"),
                    text="Sürükle=bölge · Sağ tık=hücre · Kenar tutamaç=kırp · Enter=çek · Esc=iptal",
                )
                return
            for i, (a, b, c, d) in enumerate(state.get("regions") or []):
                cv.create_rectangle(a, b, c, d, outline="#00e5ff", width=2, tags="sel")
                cv.create_rectangle(a, b, c, d, outline="", fill="#00e5ff", stipple="gray25", tags="sel")
            if state["ready"] or state["dragging"]:
                x1, y1, x2, y2 = state["x1"], state["y1"], state["x2"], state["y2"]
                cv.create_rectangle(x1, y1, x2, y2, outline="#e94560", width=2, tags="sel")
                cv.create_rectangle(x1, y1, x2, y2, outline="", fill="#e94560", stipple="gray25", tags="sel")
                if state["ready"] and not state.get("rbtn"):
                    for name, (hx, hy) in handles().items():
                        cv.create_rectangle(
                            hx - HR, hy - HR, hx + HR, hy + HR,
                            fill="#ffffff", outline="#e94560", width=2, tags="hnd",
                        )
            cv.delete("hint")
            nreg = len(state.get("regions") or [])
            if state["ready"]:
                tip = "Kenar tutamaçlarından kırp · Enter=çek · Esc=iptal · Yeni bölge için dışarı sürükle"
            else:
                tip = "Sürükle=bölge · Sağ basılı=çoklu hücre · Enter=çek · Esc=iptal"
            cv.create_text(
                12, 12, anchor="nw", fill="white", tags="hint",
                font=("Segoe UI", 11, "bold"),
                text=tip,
            )

        def cell_at(px, py):
            xs = xs_d if xs_d else [0, int(fw * ratio)]
            ys = ys_d if ys_d else [0, int(fh * ratio)]
            left = max([x for x in xs if x <= px], default=0)
            right = min([x for x in xs if x > px], default=int(fw * ratio))
            top = max([y for y in ys if y <= py], default=0)
            bot = min([y for y in ys if y > py], default=int(fh * ratio))
            if right - left < 2 or bot - top < 2:
                return None
            return left, top, right, bot

        def on_press(e):
            h = hit_handle(e.x, e.y)
            if h:
                state["handle"] = h
                state["dragging"] = True
                state["crop_edit"] = True
                return
            # Seçim kutusunun içinde (tutamaç dışı) tık → yeni seçim başlatma
            if state["ready"]:
                x1, x2 = sorted([state["x1"], state["x2"]])
                y1, y2 = sorted([state["y1"], state["y2"]])
                if x1 <= e.x <= x2 and y1 <= e.y <= y2:
                    state["handle"] = None
                    state["dragging"] = False
                    return
            state["handle"] = None
            state["dragging"] = True
            state["ready"] = False
            state["crop_edit"] = False
            x, y = snap_val(e.x, xs_d), snap_val(e.y, ys_d)
            state["x1"] = state["x2"] = x
            state["y1"] = state["y2"] = y

        def on_drag(e):
            if not state["dragging"]:
                return
            if state["handle"]:
                hx = snap_val(e.x, xs_d)
                hy = snap_val(e.y, ys_d)
                h = state["handle"]
                if "w" in h or h == "w":
                    state["x1"] = hx
                if "e" in h or h == "e":
                    state["x2"] = hx
                if "n" in h or h == "n":
                    state["y1"] = hy
                if "s" in h or h == "s":
                    state["y2"] = hy
                # corner names
                if h in ("nw", "sw"):
                    state["x1"] = hx
                if h in ("ne", "se"):
                    state["x2"] = hx
                if h in ("nw", "ne"):
                    state["y1"] = hy
                if h in ("sw", "se"):
                    state["y2"] = hy
                state["ready"] = True
            else:
                state["x2"] = snap_val(e.x, xs_d)
                state["y2"] = snap_val(e.y, ys_d)
                state["ready"] = True
            draw_sel()

        def on_release(e):
            if state["dragging"]:
                was_handle = state.get("handle")
                state["dragging"] = False
                state["handle"] = None
                norm_box()
                state["ready"] = abs(state["x2"] - state["x1"]) > 3 and abs(state["y2"] - state["y1"]) > 3
                # Seçim tamamlanınca kırpma tutamaçlarını otomatik göster
                if state["ready"] and not was_handle:
                    state["crop_edit"] = True
                elif state["ready"] and was_handle:
                    state["crop_edit"] = True
                draw_sel()

        def on_right_press(e):
            state["rbtn"] = True
            cell = cell_at(e.x, e.y)
            if cell:
                state["x1"], state["y1"], state["x2"], state["y2"] = cell
                state["ready"] = True
                state["crop_edit"] = True
                box = (min(cell[0], cell[2]), min(cell[1], cell[3]), max(cell[0], cell[2]), max(cell[1], cell[3]))
                if box not in state["regions"]:
                    state["regions"].append(box)
                draw_sel()

        def on_right_drag(e):
            if not state.get("rbtn"):
                return
            cell = cell_at(e.x, e.y)
            if not cell:
                return
            box = (min(cell[0], cell[2]), min(cell[1], cell[3]), max(cell[0], cell[2]), max(cell[1], cell[3]))
            state["x1"], state["y1"], state["x2"], state["y2"] = box
            state["ready"] = True
            state["crop_edit"] = True
            if box not in state["regions"]:
                state["regions"].append(box)
            draw_sel()

        def on_right_release(e):
            state["rbtn"] = False
            if state.get("ready"):
                state["crop_edit"] = True
                draw_sel()

        def finish(ok=True):
            try:
                overlay.destroy()
            except Exception:
                pass
            self.root.deiconify()
            self.root.lift()
            if not ok:
                return
            # Toplanan bölgeler + aktif seçim
            boxes = list(state.get("regions") or [])
            if state.get("ready"):
                norm_box()
                boxes.append((state["x1"], state["y1"], state["x2"], state["y2"]))
            # benzersiz
            uniq = []
            for b in boxes:
                x1, y1, x2, y2 = min(b[0], b[2]), min(b[1], b[3]), max(b[0], b[2]), max(b[1], b[3])
                if x2 - x1 >= 4 and y2 - y1 >= 4:
                    t = (x1, y1, x2, y2)
                    if t not in uniq:
                        uniq.append(t)
            if not uniq:
                self.status_label.config(text="Bölge seçilmedi", fg=self.colors["warning"])
                return

            def snap_i(v, anchors):
                best, bd = v, 16
                for a in anchors:
                    if abs(v - a) < bd:
                        best, bd = a, abs(v - a)
                return best

            # Tüm seçimleri tek dikdörtgende birleştir (tek nesne)
            ux1 = min(b[0] for b in uniq)
            uy1 = min(b[1] for b in uniq)
            ux2 = max(b[2] for b in uniq)
            uy2 = max(b[3] for b in uniq)
            fx1, fy1 = int(ux1 / ratio), int(uy1 / ratio)
            fx2, fy2 = int(ux2 / ratio), int(uy2 / ratio)
            fx1, fx2 = snap_i(fx1, snap_xs), snap_i(fx2, snap_xs)
            fy1, fy2 = snap_i(fy1, snap_ys), snap_i(fy2, snap_ys)
            fx1, fx2 = max(0, min(fx1, fx2)), min(fw, max(fx1, fx2))
            fy1, fy2 = max(0, min(fy1, fy2)), min(fh, max(fy1, fy2))
            if fx2 - fx1 < 2 or fy2 - fy1 < 2:
                return
            crop = full.crop((fx1, fy1, fx2, fy2))

            # Ekle veya yeni sayfa
            choice = {"mode": None}
            dlg = tk.Toplevel(self.root)
            dlg.title("Ekran görüntüsü")
            dlg.configure(bg=self.colors["bg_medium"])
            dlg.transient(self.root)
            dlg.grab_set()
            dlg.resizable(False, False)
            tk.Label(
                dlg, text=f"📷 {crop.width}×{crop.height}\nNasıl açılsın?",
                bg=self.colors["bg_medium"], fg=self.colors["text"],
                font=("Segoe UI", 11, "bold"), justify="center",
            ).pack(padx=20, pady=(16, 10))
            fr = tk.Frame(dlg, bg=self.colors["bg_medium"])
            fr.pack(pady=(0, 16))

            def pick(m):
                choice["mode"] = m
                dlg.destroy()

            tk.Button(
                fr, text="➕ Çalışmaya ekle", command=lambda: pick("add"),
                bg=self.colors["accent"], fg="white", relief="flat",
                font=("Segoe UI", 10, "bold"), padx=12, pady=8, cursor="hand2",
            ).pack(side=tk.LEFT, padx=6)
            tk.Button(
                fr, text="🆕 Yeni sayfa", command=lambda: pick("new"),
                bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
                font=("Segoe UI", 10, "bold"), padx=12, pady=8, cursor="hand2",
            ).pack(side=tk.LEFT, padx=6)
            dlg.update_idletasks()
            try:
                x = self.root.winfo_rootx() + 80
                y = self.root.winfo_rooty() + 80
                dlg.geometry(f"+{x}+{y}")
            except Exception:
                pass
            self.root.wait_window(dlg)
            if not choice["mode"]:
                return

            self.save_state()
            if choice["mode"] == "new":
                self.original_image = Image.new("RGBA", (crop.width, crop.height), (255, 255, 255, 255))
                self.objects = [{
                    "type": "image",
                    "layer": self.current_layer_id,
                    "x1": 0.0, "y1": 0.0,
                    "x2": float(crop.width), "y2": float(crop.height),
                    "pil_image": crop,
                    "opacity": 100,
                    "name": "Screenshot",
                    "locked": False,
                }]
                self.selected_obj = None
                self.selected_objs = []
                self.history = []
                self.redo_stack = []
                self.scale = 1.0
                self.pan_x = self.pan_y = 0
                msg = f"📷 Yeni sayfa — {crop.width}×{crop.height}"
            else:
                # mevcut sayfaya nesne olarak ekle
                if not self.original_image:
                    self.original_image = Image.new("RGBA", (max(800, crop.width), max(600, crop.height)), (255, 255, 255, 255))
                pw, ph = self.original_image.size
                # ortala veya sol üst yakın
                x1 = max(0, (pw - crop.width) / 2)
                y1 = max(0, (ph - crop.height) / 2)
                # taşarsa büyüt sayfa
                need_w = int(max(pw, x1 + crop.width))
                need_h = int(max(ph, y1 + crop.height))
                if need_w > pw or need_h > ph:
                    canvas = Image.new("RGBA", (need_w, need_h), (255, 255, 255, 255))
                    canvas.paste(self.original_image, (0, 0))
                    self.original_image = canvas
                self.objects.append({
                    "type": "image",
                    "layer": self.current_layer_id,
                    "x1": float(x1), "y1": float(y1),
                    "x2": float(x1 + crop.width), "y2": float(y1 + crop.height),
                    "pil_image": crop,
                    "opacity": 100,
                    "name": "Screenshot",
                    "locked": False,
                })
                self.selected_obj = None
                self.selected_objs = []
                msg = f"📷 Çalışmaya eklendi — {crop.width}×{crop.height}"

            self.dirty = True
            self.invalidate_cache()
            self.redraw()
            self.root.after(50, self.focus_view)
            self.set_action("move")
            self.status_label.config(text=msg + " · Seç aracı", fg=self.colors["success"])

        cv.bind("<ButtonPress-1>", on_press)
        cv.bind("<B1-Motion>", on_drag)
        cv.bind("<ButtonRelease-1>", on_release)
        cv.bind("<ButtonPress-3>", on_right_press)
        cv.bind("<B3-Motion>", on_right_drag)
        cv.bind("<ButtonRelease-3>", on_right_release)
        def toggle_crop_edit(e=None):
            if not state.get("ready") and not state.get("regions"):
                return
            # aktif seçim yoksa regions'tan sonuncuyu al
            if not state.get("ready") and state.get("regions"):
                box = state["regions"][-1]
                state["x1"], state["y1"], state["x2"], state["y2"] = box
                state["ready"] = True
            state["crop_edit"] = not state.get("crop_edit")
            state["handle"] = None
            state["dragging"] = False
            draw_sel()

        def on_escape(e=None):
            if state.get("crop_edit"):
                state["crop_edit"] = False
                state["handle"] = None
                draw_sel()
                return
            finish(False)

        overlay.bind("<Return>", lambda e: finish(True) if (state.get("ready") or state.get("regions")) else None)
        overlay.bind("<KP_Enter>", lambda e: finish(True) if (state.get("ready") or state.get("regions")) else None)
        overlay.bind("<Escape>", on_escape)
        overlay.bind("<Key-c>", toggle_crop_edit)
        overlay.bind("<Key-C>", toggle_crop_edit)
        cv.bind("<Key-c>", toggle_crop_edit)
        cv.bind("<Key-C>", toggle_crop_edit)
        try:
            overlay.focus_force()
            cv.focus_set()
        except Exception:
            pass
        draw_sel()

    def open_image(self):
        filepath = filedialog.askopenfilename(
            title="Resim Aç",
            filetypes=[
                ("PNG / JPEG", "*.png *.jpg *.jpeg"),
                ("PNG", "*.png"),
                ("JPEG", "*.jpg *.jpeg"),
            ],
        )
        if filepath:
            self.original_image = Image.open(filepath).convert("RGBA")
            self.objects = []
            self.selected_obj = None
            self.history = []
            self.redo_stack = []
            self.invalidate_cache()
            self.scale = 1.0
            self.pan_x = 0
            self.pan_y = 0
            self.drag_items = []
            self.temp_items = []
            self.canvas.delete("all")
            
            cw = self.canvas.winfo_width()
            ch = self.canvas.winfo_height()
            if cw > 1 and ch > 1:
                iw, ih = self.original_image.size
                self.scale = min((cw - 40) / iw, (ch - 40) / ih)
            self._initial_scale = self.scale

            self.dirty = False
            self.project_path = None
            name = filepath.replace("\\", "/").split("/")[-1]
            self.redraw()
            self.start_page_edge_crop()
            self.status_label.config(
                text=f"📂 {name} — kenar tutamaçlarından kırp | Enter: uygula | Esc: iptal",
                fg=self.colors["success"]
            )

    def _on_mousewheel(self, event):
        # Windows: delta 120 birim; daha yumuşak adım
        steps = event.delta / 120.0 if event.delta else (1 if getattr(event, 'num', 0) == 4 else -1)
        # Photo Viewer tarzı yumuşak faktör
        factor = 1.08 ** steps if steps > 0 else (1 / 1.08) ** abs(steps)
        self.zoom(factor, focus_x=event.x, focus_y=event.y)

    def _max_scale(self):
        """Üst ölçek — yüksek çözünürlükte daha fazla yaklaşmaya izin ver."""
        iw, ih = self.original_image.size
        max_pixels = 5_000_000  # akıcı zoom + kabul edilebilir HQ
        area = max(1, iw * ih)
        return max(0.05, (max_pixels / area) ** 0.5)

    def zoom(self, factor, focus_x=None, focus_y=None):
        """İmleç merkezli smooth zoom (Windows Fotoğraf Görüntüleyici tarzı)."""
        if not self.original_image:
            return

        old_scale = self.scale
        new_scale = max(0.05, min(old_scale * factor, self._max_scale()))
        if abs(new_scale - old_scale) < 1e-6:
            return

        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if focus_x is None:
            focus_x = cw / 2
        if focus_y is None:
            focus_y = ch / 2

        # Zoom öncesi imleç altındaki sayfa noktası
        img_x = getattr(self, 'img_x', 0)
        img_y = getattr(self, 'img_y', 0)
        wx = (focus_x - img_x - self.pan_x) / old_scale
        wy = (focus_y - img_y - self.pan_y) / old_scale

        self.scale = new_scale
        self._interaction_mode = True

        # Yeni boyuta göre img_x/y + imleç altı nokta sabit kalsın
        new_w = max(1, int(round(self.original_image.width * new_scale)))
        new_h = max(1, int(round(self.original_image.height * new_scale)))
        if cw > 1 and ch > 1:
            self.img_x = max(0, (cw - new_w) // 2)
            self.img_y = max(0, (ch - new_h) // 2)
        self.pan_x = focus_x - self.img_x - wx * new_scale
        self.pan_y = focus_y - self.img_y - wy * new_scale

        self._blit_cached_viewport(precomputed_size=(new_w, new_h))

        if self._zoom_after_id is not None:
            try:
                self.root.after_cancel(self._zoom_after_id)
            except Exception:
                pass
        # Biraz daha uzun idle → kesintisiz tekerlek hissi
        self._zoom_after_id = self.root.after(200, self._finish_interaction_redraw)

    def _finish_interaction_redraw(self):
        self._zoom_after_id = None
        self._interaction_mode = False
        self.redraw()

    def _blit_cached_viewport(self, precomputed_size=None):
        """Hızlı zoom: büyük ölçekte tüm sayfayı değil, görünen alanı ölçekle."""
        if self._hq_pil is None or self._hq_scale is None or self._hq_scale <= 0:
            self.redraw()
            return

        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw <= 1 or ch <= 1:
            return

        ratio = self.scale / self._hq_scale
        src_img = self._hq_pil
        full_w = max(1, int(round(src_img.width * ratio)))
        full_h = max(1, int(round(src_img.height * ratio)))

        if precomputed_size is None:
            self.img_x = max(0, (cw - full_w) // 2)
            self.img_y = max(0, (ch - full_h) // 2)

        # Sayfa ekranın dışına taşıyorsa: sadece görünen dikdörtgeni işle (kasma engeli)
        page_left = self.img_x + self.pan_x
        page_top = self.img_y + self.pan_y
        # Canvas'ta görünen sayfa bölgesi (ekran px)
        vis_l = max(0, page_left)
        vis_t = max(0, page_top)
        vis_r = min(cw, page_left + full_w)
        vis_b = min(ch, page_top + full_h)

        if vis_r <= vis_l or vis_b <= vis_t:
            # Hiç görünmüyor
            return

        out_w = max(1, int(vis_r - vis_l))
        out_h = max(1, int(vis_b - vis_t))

        # Kaynak (HQ) üzerinde karşılık gelen kırpma
        # full görüntü koordinatı: screen - page_left
        src_l = (vis_l - page_left) / ratio
        src_t = (vis_t - page_top) / ratio
        src_r = (vis_r - page_left) / ratio
        src_b = (vis_b - page_top) / ratio

        src_l = max(0, min(src_img.width, int(src_l)))
        src_t = max(0, min(src_img.height, int(src_t)))
        src_r = max(src_l + 1, min(src_img.width, int(math.ceil(src_r))))
        src_b = max(src_t + 1, min(src_img.height, int(math.ceil(src_b))))

        try:
            crop = src_img.crop((src_l, src_t, src_r, src_b))
            # Etkileşimde NEAREST = akıcı; HQ settle'da zaten full redraw
            if crop.size != (out_w, out_h):
                crop = crop.resize((out_w, out_h), Image.Resampling.NEAREST)
            fast = crop
        except Exception:
            # Fallback: küçükse full resize
            try:
                if full_w * full_h > cw * ch * 4:
                    # yine de sınırla
                    tw = min(full_w, cw * 2)
                    th = min(full_h, ch * 2)
                    fast = src_img.resize((max(1, tw), max(1, th)), Image.Resampling.NEAREST)
                    full_w, full_h = fast.size
                    self.img_x = max(0, (cw - full_w) // 2)
                    self.img_y = max(0, (ch - full_h) // 2)
                    page_left = self.img_x + self.pan_x
                    page_top = self.img_y + self.pan_y
                else:
                    fast = src_img.resize((full_w, full_h), Image.Resampling.NEAREST)
            except Exception:
                self.redraw()
                return
            self.rendered_objects_img = ImageTk.PhotoImage(fast)
            self._view_scale = self.scale
            self.canvas.delete("selection_ui")
            self.canvas.delete("movable")
            items = self.canvas.find_withtag("bg_image")
            if items:
                self.canvas.coords(items[0], page_left, page_top)
                self.canvas.itemconfig(items[0], image=self.rendered_objects_img)
            else:
                self.canvas.create_image(page_left, page_top, anchor=tk.NW,
                                        image=self.rendered_objects_img, tags="bg_image")
                self.canvas.tag_lower("bg_image")
            return

        self.rendered_objects_img = ImageTk.PhotoImage(fast)
        self._view_scale = self.scale
        # Görünen parçanın sol üstü ekranda vis_l, vis_t
        # Hit-test için img_x/pan mantığı: tüm sayfa hâlâ full_w/full_h mantığında
        # bg_image'ı görünen parçaya koy
        draw_x = vis_l
        draw_y = vis_t

        self.canvas.delete("selection_ui")
        self.canvas.delete("movable")
        items = self.canvas.find_withtag("bg_image")
        if items:
            self.canvas.coords(items[0], draw_x, draw_y)
            self.canvas.itemconfig(items[0], image=self.rendered_objects_img)
        else:
            self.canvas.create_image(
                draw_x, draw_y, anchor=tk.NW,
                image=self.rendered_objects_img, tags="bg_image"
            )
            self.canvas.tag_lower("bg_image")

    def focus_view(self):
        """Mevcut sayfayı ekrana sığdır (fit) ve ortala."""
        if not self.original_image:
            return
        self.root.update_idletasks()
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw <= 1 or ch <= 1:
            self.root.after(50, self.focus_view)
            return

        iw, ih = self.original_image.size
        margin = 40
        fit = min((cw - margin) / max(1, iw), (ch - margin) / max(1, ih))
        if fit <= 0:
            fit = 1.0

        self.scale = fit
        self.pan_x = 0
        self.pan_y = 0
        self.invalidate_cache()
        self.redraw()
        self.status_label.config(
            text=f"🎯 Ekrana sığdırıldı — ölçek {self.scale:.0%}",
            fg=self.colors["success"]
        )

    def reset_view(self):
        """Orijinal 1:1 piksel boyutu (ilk açılış gerçek boyutu)."""
        if not self.original_image:
            return
        self.root.update_idletasks()
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw <= 1 or ch <= 1:
            self.root.after(50, self.reset_view)
            return

        # Gerçek orijinal: 1 ekran pikseli = 1 resim pikseli
        self.scale = 1.0
        # Büyük resmi ortala (pan ile)
        page_w = self.original_image.width * self.scale
        page_h = self.original_image.height * self.scale
        self.img_x = max(0, int((cw - page_w) // 2))
        self.img_y = max(0, int((ch - page_h) // 2))
        # Sayfa canvas'tan büyükse merkeze hizala
        if page_w > cw:
            self.pan_x = (cw - page_w) / 2.0 - self.img_x
        else:
            self.pan_x = 0
        if page_h > ch:
            self.pan_y = (ch - page_h) / 2.0 - self.img_y
        else:
            self.pan_y = 0

        self.invalidate_cache()
        self.redraw()
        iw, ih = self.original_image.size
        self.status_label.config(
            text=f"↺ 1:1 orijinal — {iw}×{ih} px (ölçek 100%)",
            fg=self.colors["success"]
        )

    def _group_members(self, obj):
        """Nesne grupluysa tüm üyeler, değilse [obj]."""
        if not obj:
            return []
        gid = obj.get("group_id")
        if not gid:
            return [obj]
        return [o for o in self.objects if o.get("group_id") == gid] or [obj]

    def _update_props_bar(self, force_show=None):
        """Şekil/metin seçiliyken stil paneli; resimde gizle."""
        panel = getattr(self, "_style_panel", None)
        if panel is None:
            return
        obj = self.selected_obj
        t = obj.get("type") if obj else None
        if force_show is None:
            show = bool(obj) and t not in ("image", "fill_region")
        else:
            show = bool(force_show)
        try:
            if show:
                if not panel.winfo_ismapped():
                    panel.pack(fill=tk.X, padx=4, pady=(4, 8))
                self._props_bar_visible = True
                self._sync_style_panel_mode(t)
            else:
                if panel.winfo_ismapped():
                    panel.pack_forget()
                self._props_bar_visible = False
        except Exception:
            pass

    def _sync_style_panel_mode(self, obj_type):
        """Türe göre stil satırlarını göster/gizle. Aksiyonlar her zaman en altta."""
        is_text = obj_type in ("text", "textbox")
        is_stroke_only = obj_type in ("pen", "curve", "arrow", "arrow_path")
        # outline: text yok; diğerlerinde var
        # fill: sadece dolgulu şekiller
        # thickness: text yok
        # font color/size: text ve etiketli şekiller (stroke_only değil)
        rows = {
            "outline": getattr(self, "_style_row_outline", None),
            "fill": getattr(self, "_style_row_fill", None),
            "thickness": getattr(self, "_style_row_thickness", None),
            "font_color": getattr(self, "_style_row_font_color", None),
            "fontsize": getattr(self, "_style_row_fontsize", None),
            "opacity": getattr(self, "opacity_scale", None) and self.opacity_scale.master,
            "actions": getattr(self, "_style_row_actions", None),
        }
        show = {
            "outline": not is_text,
            "fill": not is_text and not is_stroke_only,
            "thickness": not is_text,
            "font_color": not is_stroke_only,
            "fontsize": not is_stroke_only,
            "opacity": True,
            "actions": True,
        }
        # önce hepsini unmap
        for key, row in rows.items():
            if row is None:
                continue
            try:
                row.pack_forget()
            except Exception:
                pass
        # sırayla yeniden pack
        order = ("outline", "font_color", "fill", "thickness", "fontsize", "opacity", "actions")
        for key in order:
            if not show.get(key):
                continue
            row = rows.get(key)
            if row is None:
                continue
            try:
                if key == "actions":
                    row.pack(fill=tk.X, padx=8, pady=(4, 8))
                else:
                    row.pack(fill=tk.X, padx=8, pady=2)
            except Exception:
                pass
        try:
            obj = self.selected_obj
            if obj and getattr(self, "btn_font_color", None):
                c = obj.get("label_color") or obj.get("color") or self.outline_color
                self.btn_font_color.config(bg=c, activebackground=c)
        except Exception:
            pass

    def _set_selection(self, objs, expand_groups=True):
        """Toplu seçimi güncelle; selected_obj = son birincil.\nexpand_groups: seçilenlerin grup arkadaşlarını da ekle.\n"""
        seen = []
        for o in objs:
            if o is not None and o in self.objects and o not in seen:
                seen.append(o)
        if expand_groups:
            gids = {o.get("group_id") for o in seen if o.get("group_id")}
            if gids:
                for o in self.objects:
                    if o.get("group_id") in gids and o not in seen:
                        seen.append(o)
        self.selected_objs = seen
        self.selected_obj = seen[-1] if seen else None
        try:
            self._update_props_bar()
        except Exception:
            pass
        try:
            if getattr(self, "btn_style_lock", None):
                if self.selected_obj and self._is_locked(self.selected_obj):
                    self.btn_style_lock.config(text="🔓 Kilidi aç")
                else:
                    self.btn_style_lock.config(text="🔒 Kilitle")
        except Exception:
            pass

    def update_group_ui(self):
        if not hasattr(self, "group_listbox"):
            return
        self.group_listbox.delete(0, tk.END)
        # aktif gruplar (en az 1 üye)
        active = {}
        for o in self.objects:
            gid = o.get("group_id")
            if gid:
                active.setdefault(gid, 0)
                active[gid] += 1
        # silinmiş grupları temizle
        for gid in list(self.groups.keys()):
            if gid not in active:
                del self.groups[gid]
        self._group_list_ids = []
        for gid, info in sorted(self.groups.items(), key=lambda x: x[0]):
            n = active.get(gid, 0)
            if n <= 0:
                continue
            name = info.get("name", f"Grup {gid}")
            self.group_listbox.insert(tk.END, f"🧩 {name} ({n})")
            self._group_list_ids.append(gid)

    def on_group_select(self, event):
        sel = self.group_listbox.curselection()
        if not sel:
            return
        ids = getattr(self, "_group_list_ids", [])
        if sel[0] >= len(ids):
            return
        gid = ids[sel[0]]
        members = [o for o in self.objects if o.get("group_id") == gid]
        self._set_selection(members, expand_groups=False)
        self.draw_selection_ui()
        name = self.groups.get(gid, {}).get("name", f"Grup {gid}")
        self.status_label.config(text=f"🧩 {name} — {len(members)} üye seçildi", fg=self.colors["success"])

    def group_selected(self):
        """Seçili nesneleri grupla."""
        members = [o for o in self.selected_objs if o in self.objects]
        if len(members) < 2:
            self.status_label.config(text="Grup için en az 2 nesne seç (Ctrl+tık veya kutu)", fg=self.colors["warning"])
            return
        name = simpledialog.askstring(
            "Grup adı", "Grup ismi:",
            initialvalue=f"Grup {self.group_counter}",
            parent=self.root,
        )
        if not name or not name.strip():
            return
        self.save_state()
        gid = self.group_counter
        self.group_counter += 1
        self.groups[gid] = {"id": gid, "name": name.strip()}
        for o in members:
            o["group_id"] = gid
        self._set_selection(members, expand_groups=False)
        self.update_group_ui()
        self.draw_selection_ui()
        self.status_label.config(text=f"🔗 Gruplandı: {name.strip()} ({len(members)} üye)", fg=self.colors["success"])

    def ungroup_selected(self):
        """Seçili nesnelerin grubunu çöz."""
        members = [o for o in self.selected_objs if o in self.objects and o.get("group_id")]
        if not members:
            # listeden seçili grup
            sel = self.group_listbox.curselection() if hasattr(self, "group_listbox") else ()
            ids = getattr(self, "_group_list_ids", [])
            if sel and sel[0] < len(ids):
                gid = ids[sel[0]]
                members = [o for o in self.objects if o.get("group_id") == gid]
        if not members:
            self.status_label.config(text="Çözülecek grup yok", fg=self.colors["warning"])
            return
        self.save_state()
        gids = {o.get("group_id") for o in members}
        for o in self.objects:
            if o.get("group_id") in gids:
                o.pop("group_id", None)
        for gid in gids:
            self.groups.pop(gid, None)
        self.update_group_ui()
        self.draw_selection_ui()
        self.status_label.config(text="⛓ Grup çözüldü", fg=self.colors["success"])

    def rename_group(self):
        sel = self.group_listbox.curselection() if hasattr(self, "group_listbox") else ()
        ids = getattr(self, "_group_list_ids", [])
        gid = None
        if sel and sel[0] < len(ids):
            gid = ids[sel[0]]
        elif self.selected_objs:
            for o in self.selected_objs:
                if o.get("group_id"):
                    gid = o["group_id"]
                    break
        if gid is None or gid not in self.groups:
            self.status_label.config(text="Önce bir grup seç", fg=self.colors["warning"])
            return
        old = self.groups[gid].get("name", f"Grup {gid}")
        name = simpledialog.askstring("Grup adı", "Yeni isim:", initialvalue=old, parent=self.root)
        if name and name.strip():
            self.save_state()
            self.groups[gid]["name"] = name.strip()
            self.update_group_ui()
            self.status_label.config(text=f"✏️ Grup: {name.strip()}", fg=self.colors["success"])

    def delete_selected_object(self):
        targets = list(self.selected_objs) if self.selected_objs else ([self.selected_obj] if self.selected_obj else [])
        targets = [o for o in targets if o in self.objects]
        if not targets:
            return
        locked = [o for o in targets if self._is_locked(o)]
        targets = [o for o in targets if not self._is_locked(o)]
        if not targets:
            self.status_label.config(text="🔒 Kilitli nesne silinemez", fg=self.colors["warning"])
            return
        self.save_state()
        for o in targets:
            try:
                self.objects.remove(o)
            except ValueError:
                pass
        self.selected_obj = None
        self.selected_objs = []
        self.redraw()
        if locked:
            self.status_label.config(text=f"🔒 {len(locked)} kilitli nesne atlandı", fg=self.colors["warning"])

    def _is_locked(self, obj):
        if not obj:
            return False
        v = obj.get("locked")
        return v is True or v == 1 or v == "1" or str(v).lower() == "true"

    def unlock_all(self):
        """Tüm kilitleri aç (kilitli seçilemediği için)."""
        locked = [o for o in self.objects if self._is_locked(o)]
        if not locked:
            self.status_label.config(text="Kilitli nesne yok", fg=self.colors["text"])
            return
        self.save_state()
        for o in locked:
            o["locked"] = False
        self.invalidate_cache()
        self.redraw()
        self.draw_selection_ui()
        self.status_label.config(text=f"🔓 {len(locked)} kilidin hepsi açıldı", fg=self.colors["success"])

    def toggle_lock_selected(self):
        """Seçili nesneleri kilitle / kilidi aç."""
        targets = list(self.selected_objs) if self.selected_objs else (
            [self.selected_obj] if self.selected_obj else []
        )
        targets = [o for o in targets if o in self.objects]
        if not targets:
            self.status_label.config(text="Kilitlemek için nesne seç", fg=self.colors["warning"])
            return
        # çoğunluk kilitliyse aç, değilse kilitle
        majority_locked = sum(1 for o in targets if self._is_locked(o)) > len(targets) / 2
        self.save_state()
        new_val = not majority_locked
        for o in targets:
            o["locked"] = bool(new_val)
        # kilitlenenleri seçimden çıkar
        if new_val:
            self.selected_objs = [o for o in self.selected_objs if not self._is_locked(o)]
            if self.selected_obj and self._is_locked(self.selected_obj):
                self.selected_obj = self.selected_objs[-1] if self.selected_objs else None
        self._multi_drag = False
        self.resize_handle = None
        self.invalidate_cache()
        self.redraw()
        self.draw_selection_ui()
        n = len(targets)
        if majority_locked:
            self.status_label.config(text=f"🔓 {n} nesnenin kilidi açıldı", fg=self.colors["success"])
        else:
            self.status_label.config(text=f"🔒 {n} nesne kilitlendi", fg=self.colors["success"])
        try:
            if getattr(self, "btn_style_lock", None) and self.selected_obj:
                if self._is_locked(self.selected_obj):
                    self.btn_style_lock.config(text="🔓 Kilidi aç")
                else:
                    self.btn_style_lock.config(text="🔒 Kilitle")
        except Exception:
            pass


    def bring_forward(self):
        if self.selected_obj and self.selected_obj in self.objects:
            self.save_state()
            idx = self.objects.index(self.selected_obj)
            if idx < len(self.objects) - 1:
                self.objects[idx], self.objects[idx+1] = self.objects[idx+1], self.objects[idx]
                self.redraw()

    def send_backward(self):
        if self.selected_obj and self.selected_obj in self.objects:
            self.save_state()
            idx = self.objects.index(self.selected_obj)
            if idx > 0:
                self.objects[idx], self.objects[idx-1] = self.objects[idx-1], self.objects[idx]
                self.redraw()

    def bring_to_front(self):
        if self.selected_obj and self.selected_obj in self.objects:
            self.save_state()
            self.objects.remove(self.selected_obj)
            self.objects.append(self.selected_obj)
            self.redraw()

    def send_to_back(self):
        if self.selected_obj and self.selected_obj in self.objects:
            self.save_state()
            self.objects.remove(self.selected_obj)
            self.objects.insert(0, self.selected_obj)
            self.redraw()
            
    def copy_object(self, event=None):
        if self.selected_obj:
            self.clipboard = self._clone_objects([self.selected_obj])[0]
            self.status_label.config(text="📋 Nesne kopyalandı", fg=self.colors["warning"])

    def paste_object(self, event=None):
        if self.clipboard:
            self.save_state()
            new_obj = self._clone_objects([self.clipboard])[0]
            new_obj['x1'] = new_obj.get('x1', 0) + 20
            new_obj['y1'] = new_obj.get('y1', 0) + 20
            if 'x2' in new_obj:
                new_obj['x2'] += 20
                new_obj['y2'] += 20
            if 'points' in new_obj:
                new_obj['points'] = [(p[0] + 20, p[1] + 20) for p in new_obj['points']]
            new_obj['layer'] = self.current_layer_id
            self.objects.append(new_obj)
            self.selected_obj = new_obj
            self.redraw()
            self.status_label.config(text="📋 Nesne yapıştırıldı", fg=self.colors["success"])

    def update_layer_ui(self):
        self.layer_listbox.delete(0, tk.END)
        for layer in reversed(self.layers):
            self.layer_listbox.insert(tk.END, ("👁 " if layer["visible"] else "❌ ") + layer["name"])
        for idx, layer in enumerate(reversed(self.layers)):
            if layer["id"] == self.current_layer_id: 
                self.layer_listbox.select_set(idx)
        self.update_group_ui()

    def on_layer_select(self, event):
        selection = self.layer_listbox.curselection()
        if selection:
            self.current_layer_id = self.layers[len(self.layers) - 1 - selection[0]]["id"]
            self.status_label.config(text=f"📑 {self.layers[len(self.layers) - 1 - selection[0]]['name']} seçildi", fg=self.colors["text"])

    def add_layer(self):
        self.save_state()
        self.layers.append({"id": self.layer_counter, "name": f"Katman {self.layer_counter + 1}", "visible": True})
        self.current_layer_id = self.layer_counter
        self.layer_counter += 1
        self.update_layer_ui()
        self.status_label.config(text=f"➕ Yeni katman eklendi", fg=self.colors["success"])

    def rename_layer(self):
        """Seçili katmana isim ver."""
        layer = None
        for L in self.layers:
            if L["id"] == self.current_layer_id:
                layer = L
                break
        if not layer:
            return
        name = simpledialog.askstring(
            "Katman adı", "Yeni isim:",
            initialvalue=layer.get("name", ""),
            parent=self.root,
        )
        if name and name.strip():
            self.save_state()
            layer["name"] = name.strip()
            self.update_layer_ui()
            self.status_label.config(text=f"✏️ Katman: {layer['name']}", fg=self.colors["success"])

    def _obj_center(self, obj):
        if obj.get("points"):
            xs = [p[0] for p in obj["points"]]
            ys = [p[1] for p in obj["points"]]
            return (min(xs) + max(xs)) / 2.0, (min(ys) + max(ys)) / 2.0
        x1, y1 = obj.get("x1", 0), obj.get("y1", 0)
        x2, y2 = obj.get("x2", x1), obj.get("y2", y1)
        return (x1 + x2) / 2.0, (y1 + y2) / 2.0

    def _rotate_obj_geometry(self, obj, degrees):
        """Nesne geometrisini merkez etrafında döndür (points / açı)."""
        if not degrees:
            return
        t = obj.get("type")
        cx, cy = self._obj_center(obj)
        if t in ("pen", "curve") and obj.get("points"):
            obj["points"] = self._rotate_points(obj["points"], cx, cy, degrees)
            xs = [p[0] for p in obj["points"]]
            ys = [p[1] for p in obj["points"]]
            obj["x1"], obj["y1"] = min(xs), min(ys)
            obj["x2"], obj["y2"] = max(xs), max(ys)
            return
        if t == "arrow" and "x1" in obj and "x2" in obj:
            (x1, y1), (x2, y2) = self._rotate_points(
                [(obj["x1"], obj["y1"]), (obj["x2"], obj["y2"])], cx, cy, degrees
            )
            obj["x1"], obj["y1"], obj["x2"], obj["y2"] = x1, y1, x2, y2
            return
        if t in ("text", "textbox"):
            # sadece konum
            pts = self._rotate_points([(obj.get("x1", 0), obj.get("y1", 0))], cx, cy, degrees)
            obj["x1"], obj["y1"] = pts[0]
            return
        if t == "image" and obj.get("pil_image") is not None:
            d = degrees % 360
            if d in (90, 270, -90, -270) or abs(d) % 180 == 90:
                try:
                    img = obj["pil_image"]
                    if d % 360 in (90, -270):
                        obj["pil_image"] = img.transpose(Image.Transpose.ROTATE_270)
                    elif d % 360 in (270, -90):
                        obj["pil_image"] = img.transpose(Image.Transpose.ROTATE_90)
                    elif d % 360 == 180:
                        obj["pil_image"] = img.transpose(Image.Transpose.ROTATE_180)
                    if abs(d) % 180 == 90:
                        x1, y1, x2, y2 = obj["x1"], obj["y1"], obj["x2"], obj["y2"]
                        cx2, cy2 = (x1 + x2) / 2, (y1 + y2) / 2
                        w, h = abs(x2 - x1), abs(y2 - y1)
                        obj["x1"], obj["y1"] = cx2 - h / 2, cy2 - w / 2
                        obj["x2"], obj["y2"] = cx2 + h / 2, cy2 + w / 2
                    obj["rotation"] = 0
                    obj.pop("_rz_cache", None)
                    return
                except Exception:
                    pass
            obj["rotation"] = (obj.get("rotation", 0) + degrees) % 360
            obj.pop("_rz_cache", None)
            return
        # rect / square / triangle / hexagon / star / callout / circle
        obj["rotation"] = (obj.get("rotation", 0) + degrees) % 360

    def _mirror_obj_geometry(self, obj, axis="h"):
        t = obj.get("type")
        cx, cy = self._obj_center(obj)
        if t in ("pen", "curve") and obj.get("points"):
            if axis == "h":
                obj["points"] = [(2 * cx - p[0], p[1]) for p in obj["points"]]
            else:
                obj["points"] = [(p[0], 2 * cy - p[1]) for p in obj["points"]]
            xs = [p[0] for p in obj["points"]]
            ys = [p[1] for p in obj["points"]]
            obj["x1"], obj["y1"] = min(xs), min(ys)
            obj["x2"], obj["y2"] = max(xs), max(ys)
            return
        if t == "arrow":
            if axis == "h":
                obj["x1"], obj["x2"] = 2 * cx - obj["x1"], 2 * cx - obj["x2"]
            else:
                obj["y1"], obj["y2"] = 2 * cy - obj["y1"], 2 * cy - obj["y2"]
            return
        if t in ("text", "textbox"):
            if axis == "h":
                obj["x1"] = 2 * cx - obj.get("x1", 0)
            else:
                obj["y1"] = 2 * cy - obj.get("y1", 0)
            return
        if t == "image" and obj.get("pil_image") is not None:
            try:
                img = obj["pil_image"]
                obj["pil_image"] = img.transpose(
                    Image.Transpose.FLIP_LEFT_RIGHT if axis == "h" else Image.Transpose.FLIP_TOP_BOTTOM
                )
                obj.pop("_rz_cache", None)
            except Exception:
                pass
            # rotasyonu ayna ile uyumlu güncelle
            rot = obj.get("rotation", 0) or 0
            if axis == "h":
                obj["rotation"] = (-rot) % 360
            else:
                obj["rotation"] = (180 - rot) % 360
            return
        # Geometrik şekiller: flip bayrağı (görünür etki için zorunlu)
        if axis == "h":
            obj["flip_h"] = not obj.get("flip_h", False)
            rot = obj.get("rotation", 0) or 0
            obj["rotation"] = (-rot) % 360
        else:
            obj["flip_v"] = not obj.get("flip_v", False)
            rot = obj.get("rotation", 0) or 0
            obj["rotation"] = (180 - rot) % 360

    def rotate_selected(self, degrees):
        targets = list(self.selected_objs) if self.selected_objs else (
            [self.selected_obj] if self.selected_obj else []
        )
        targets = [o for o in targets if o in self.objects]
        if not targets:
            self.status_label.config(text="Önce bir nesne seç", fg=self.colors["warning"])
            return
        self.save_state()
        for obj in targets:
            self._rotate_obj_geometry(obj, degrees)
        self.invalidate_cache()
        self.redraw()
        ang = targets[-1].get("rotation", 0) if targets else 0
        self.status_label.config(text=f"↻ Döndürüldü ({ang:.0f}°)", fg=self.colors["success"])

    def mirror_selected(self, axis="h"):
        targets = list(self.selected_objs) if self.selected_objs else (
            [self.selected_obj] if self.selected_obj else []
        )
        targets = [o for o in targets if o in self.objects]
        if not targets:
            self.status_label.config(text="Önce bir nesne seç", fg=self.colors["warning"])
            return
        self.save_state()
        for obj in targets:
            self._mirror_obj_geometry(obj, axis)
        self.invalidate_cache()
        self.redraw()
        self.status_label.config(
            text=f"{'↔ Yatay' if axis == 'h' else '↕ Dikey'} ayna uygulandı",
            fg=self.colors["success"],
        )

    def toggle_layer_visibility(self):
        self.save_state()
        for layer in self.layers:
            if layer["id"] == self.current_layer_id: 
                layer["visible"] = not layer["visible"]
                self.status_label.config(text=f"👁 Katman {'gizlendi' if not layer['visible'] else 'gösterildi'}", 
                                       fg=self.colors["warning"] if not layer['visible'] else self.colors["success"])
        self.update_layer_ui()
        self.redraw()

    def choose_text_bg_color(self):
        """Metin / metin kutusu arka plan rengi."""
        c = colorchooser.askcolor(
            color=self.text_bg_color or "#ffffff",
            title="Metin arka plan rengi",
        )[1]
        if not c:
            return
        self.text_bg_color = c
        try:
            if getattr(self, "btn_text_bg", None):
                self.btn_text_bg.config(bg=c, text="")
        except Exception:
            pass
        targets = list(self.selected_objs) if self.selected_objs else (
            [self.selected_obj] if self.selected_obj else []
        )
        applied = False
        for o in targets:
            if o and o in self.objects and o.get("type") in ("text", "textbox"):
                o["bg_color"] = c
                applied = True
        if applied:
            self.invalidate_cache()
            self.redraw()
            self.status_label.config(text=f"Metin arka planı: {c}", fg=self.colors["success"])

    def clear_text_bg_color(self):
        self.text_bg_color = ""
        try:
            if getattr(self, "btn_text_bg", None):
                self.btn_text_bg.config(bg="gray", text="Yok")
        except Exception:
            pass
        targets = list(self.selected_objs) if self.selected_objs else (
            [self.selected_obj] if self.selected_obj else []
        )
        for o in targets:
            if o and o in self.objects and o.get("type") in ("text", "textbox"):
                o["bg_color"] = ""
        self.invalidate_cache()
        self.redraw()

    def choose_outline_color(self):
        """Çizgi/şekil kontur rengi — metin rengine dokunmaz."""
        c = colorchooser.askcolor()[1]
        if c:
            self.outline_color = c
            self.btn_outline_color.config(bg=c, activebackground=c)
            self._default_outline = c
            if self.selected_obj and self.selected_obj.get('type') not in ('text', 'textbox'):
                self.save_state()
                self.selected_obj['color'] = c
                self.invalidate_cache()
                self.redraw()

    def choose_label_color(self):
        """Yalnızca metin rengi: bağımsız metin veya şekil içi etiket."""
        if not self.selected_obj:
            self.status_label.config(text="Önce metin veya etiketli şekil seç", fg=self.colors["warning"])
            return
        obj = self.selected_obj
        if obj.get('type') == 'text':
            c = colorchooser.askcolor(color=obj.get('color') or self.outline_color)[1]
            if c:
                self.save_state()
                obj['color'] = c
                self.invalidate_cache()
                self.redraw()
                self.status_label.config(text=f"🔤 Metin rengi: {c}", fg=self.colors["success"])
            return
        if obj.get('label'):
            c = colorchooser.askcolor(
                color=obj.get('label_color') or self.outline_color
            )[1]
            if c:
                self.save_state()
                obj['label_color'] = c
                try:
                    if getattr(self, "btn_font_color", None):
                        self.btn_font_color.config(bg=c, activebackground=c)
                except Exception:
                    pass
                self.invalidate_cache()
                self.redraw()
                self.status_label.config(text=f"🔤 Metin rengi: {c}", fg=self.colors["success"])
            return
        self.status_label.config(
            text="Metin yok — metin aracı veya şekle çift tık ile yazı ekle",
            fg=self.colors["warning"],
        )

    def choose_snap_color(self):
        c = colorchooser.askcolor(color=self.snap_guide_color)[1]
        if c:
            self.snap_guide_color = c
            try:
                if getattr(self, "btn_snap_color", None):
                    self.btn_snap_color.config(bg=c, activebackground=c)
            except Exception:
                pass
            self.status_label.config(text=f"Snap hat rengi: {c}", fg=self.colors["success"])

    def choose_fill_color(self):
        c = colorchooser.askcolor(
            color=self.fill_color or self.outline_color or "#ffffff",
            title="Dolgu rengi",
        )[1]
        if c:
            self.fill_color = c
            self.btn_fill_color.config(bg=c, text="Renk")
            if self.selected_obj and self.selected_obj['type'] not in ['text', 'arrow', 'pen', 'curve', 'fill_region']:
                self.save_state()
                self.selected_obj['fill'] = c
                self.invalidate_cache()
                self.redraw()

    def _prompt_fill_color(self):
        """Doldur aracına geçince palet aç."""
        c = colorchooser.askcolor(
            color=self.fill_color or "#3498db",
            title="🪣 Dolgu rengi seç",
        )[1]
        if c:
            self.fill_color = c
            self.btn_fill_color.config(bg=c, text="Renk")
            self.status_label.config(
                text=f"🪣 Dolgu: {c} — kapalı alana tıkla",
                fg=self.colors["success"],
            )
        elif not self.fill_color:
            self.status_label.config(
                text="🪣 Dolgu rengi seçilmedi — Dolgu kutusundan seç",
                fg=self.colors["warning"],
            )

    def clear_fill_color(self):
        """Dolgu rengini ve seçili şekillerin iç dolgusunu kaldır."""
        self.fill_color = ""
        self.btn_fill_color.config(bg="gray", text="Yok")
        targets = list(self.selected_objs) if self.selected_objs else (
            [self.selected_obj] if self.selected_obj else []
        )
        targets = [
            o for o in targets
            if o in self.objects and o.get("type") not in ("text", "arrow", "pen", "curve")
        ]
        changed = False
        if targets:
            self.save_state()
            for o in targets:
                if o.get("fill"):
                    o["fill"] = ""
                    changed = True
            if changed:
                self.invalidate_cache()
                self.redraw()
                self.status_label.config(text="✖ Şekil içi dolgu silindi", fg=self.colors["success"])
                return

        # Son kova doldurmasını geri al (sayfa pikselleri)
        region = getattr(self, "_last_fill_region", None)
        if region and self.original_image:
            self.save_state()
            img = self.original_image
            if img.mode != "RGBA":
                img = img.convert("RGBA")
            pixels = img.load()
            for px, py in region:
                try:
                    pixels[px, py] = (255, 255, 255, 255)
                except Exception:
                    pass
            self.original_image = img
            self._last_fill_region = None
            self.invalidate_cache()
            self.redraw()
            self.status_label.config(text="✖ Son doldurma silindi", fg=self.colors["success"])
            return

        self.status_label.config(text="✖ Dolgu rengi temizlendi (Yok)", fg=self.colors["warning"])

    def set_action(self, action):
        # Yarım çizimi bırak, yeni araca geç
        if getattr(self, "action", None) != action:
            self._cancel_in_progress_draw()
            if getattr(self, "_arrow_path", None) and action != "arrow_path":
                self._cancel_arrow_path()
            # Yeni araç → yalnızca varsayılan kalınlık/font/şeffaflık (renk korunur)
            self._suspend_prop_trace = True
            try:
                self.thickness.set(self._default_thickness)
                self.font_size.set(self._default_font_size)
                self.opacity.set(self._default_opacity)
            finally:
                self._suspend_prop_trace = False
        self.action = action
        for name, btn in getattr(self, "_tool_buttons", {}).items():
            try:
                if name == action:
                    btn.config(bg=self.colors["accent"], fg="white")
                else:
                    btn.config(bg=self.colors["bg_light"], fg=self.colors["text"])
            except Exception:
                pass
        self._update_tool_badge(action)
        if action == "move":
            self.canvas.config(cursor="fleur")
        elif action == "eyedropper":
            self.canvas.config(cursor="crosshair")
        elif action == "fill":
            self.canvas.config(cursor="dotbox")
            self.root.after(30, self._prompt_fill_color)
        else:
            self.canvas.config(cursor="cross")
        if action == "crop":
            self.choose_crop_target()
            return
        if self.edge_crop:
            self.cancel_edge_crop(silent=True)
        labels = {
            "move": "Seç/Taşı", "pen": "Fırça", "rect": "Dikdörtgen", "square": "Kare",
            "circle": "Daire", "hexagon": "Altıgen", "star": "Yıldız", "callout": "Callout",
            "triangle": "Üçgen", "curve": "Eğri", "arrow": "Ok", "arrow_path": "Ok Yol", "text": "Metin",
            "fill": "Doldur", "eyedropper": "Renk Al", "crop": "Kırp", "zoom_region": "Bölge Zoom",
        }
        self.status_label.config(
            text=f"🛠 {labels.get(action, action)}",
            fg=self.colors["text"],
        )
        try:
            self.canvas.focus_force()
        except Exception:
            try:
                self.canvas.focus_set()
            except Exception:
                pass

    def choose_crop_target(self):
        """Kırp aracı: hedef sor (sayfa / resim / serbest bölge)."""
        if not self.original_image:
            return

        image_objs = [o for o in self.objects if o.get("type") == "image" and o.get("pil_image") is not None]
        selected_img = (
            self.selected_obj
            if self.selected_obj and self.selected_obj.get("type") == "image"
            else None
        )

        dlg = tk.Toplevel(self.root)
        dlg.title("Kırpma hedefi")
        dlg.configure(bg=self.colors["bg_medium"])
        dlg.resizable(False, False)
        dlg.transient(self.root)
        dlg.grab_set()

        tk.Label(
            dlg, text="Ne kırpılsın?",
            bg=self.colors["bg_medium"], fg=self.colors["text"],
            font=("Segoe UI", 12, "bold"),
        ).pack(padx=24, pady=(18, 8))

        result = {"choice": None}

        def pick(c):
            result["choice"] = c
            dlg.destroy()

        row = tk.Frame(dlg, bg=self.colors["bg_medium"])
        row.pack(pady=(4, 8), padx=16)

        tk.Button(
            row, text="📄 Sayfa kenarlarından kırp", command=lambda: pick("page"),
            bg=self.colors["accent"], fg="white", relief="flat",
            font=("Segoe UI", 10, "bold"), padx=14, pady=8, cursor="hand2",
        ).pack(fill=tk.X, pady=3)

        tk.Button(
            row, text="⬚ Bölge seçerek kırp", command=lambda: pick("region"),
            bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
            font=("Segoe UI", 10, "bold"), padx=14, pady=8, cursor="hand2",
        ).pack(fill=tk.X, pady=3)

        if selected_img:
            tk.Button(
                row, text="🖼 Seçili resmi kırp", command=lambda: pick("selected"),
                bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
                font=("Segoe UI", 10, "bold"), padx=14, pady=8, cursor="hand2",
            ).pack(fill=tk.X, pady=3)

        if image_objs:
            tk.Button(
                row, text="🖼 Resim seçip kırp", command=lambda: pick("pick"),
                bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
                font=("Segoe UI", 10, "bold"), padx=14, pady=8, cursor="hand2",
            ).pack(fill=tk.X, pady=3)

        tk.Button(
            row, text="İptal", command=lambda: pick(None),
            bg=self.colors["bg_light"], fg=self.colors["text_secondary"], relief="flat",
            font=("Segoe UI", 9), padx=14, pady=6, cursor="hand2",
        ).pack(fill=tk.X, pady=(8, 4))

        dlg.update_idletasks()
        x = self.root.winfo_rootx() + (self.root.winfo_width() - dlg.winfo_width()) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - dlg.winfo_height()) // 2
        dlg.geometry(f"+{x}+{y}")
        self.root.wait_window(dlg)

        choice = result["choice"]
        if choice == "page":
            self.start_page_edge_crop()
        elif choice == "region":
            # Mevcut bölge-sürükle kırpma (mavi dikdörtgen)
            self.action = "crop"
            self.canvas.config(cursor="cross")
            self._update_tool_badge("crop")
            for name, btn in getattr(self, "_tool_buttons", {}).items():
                try:
                    if name == "crop":
                        btn.config(bg=self.colors["accent"], fg="white")
                    else:
                        btn.config(bg=self.colors["bg_light"], fg=self.colors["text"])
                except Exception:
                    pass
            self.status_label.config(
                text="⬚ Kırpılacak bölgeyi sürükleyerek seç | Esc: iptal",
                fg=self.colors["warning"],
            )
        elif choice == "selected" and selected_img:
            self.start_image_edge_crop(selected_img)
        elif choice == "pick":
            self.action = "move"
            self.canvas.config(cursor="fleur")
            self._crop_after_select = True
            self.status_label.config(
                text="🖼 Kırpılacak resmi tıkla",
                fg=self.colors["warning"],
            )
        else:
            self.action = "move"
            self.status_label.config(text="Kırpma iptal", fg=self.colors["warning"])

    def on_property_changed(self, *args):
        if self._suspend_prop_trace or not self.selected_obj:
            return
        self.selected_obj['opacity'] = self.opacity.get()
        t = self.selected_obj.get('type')
        if t in ('text', 'textbox'):
            self.selected_obj['size'] = self.font_size.get()
            # anlık hafif önizleme (kasma yok)
            self._schedule_text_size_preview()
        elif t == 'image':
            pass
        else:
            self.selected_obj['color'] = self.outline_color
            self.selected_obj['width'] = self.thickness.get()
            self.selected_obj['fill'] = self.fill_color
            if self.selected_obj.get('label') is not None:
                self.selected_obj['label_size'] = self.font_size.get()
        if getattr(self, '_prop_after_id', None):
            try:
                self.root.after_cancel(self._prop_after_id)
            except Exception:
                pass
        # HQ yeniden çizim gecikmeli — kaydırırken akıcı
        delay = 140 if t in ('text', 'textbox') else 100
        self._prop_after_id = self.root.after(delay, self._prop_redraw)

    def _schedule_text_size_preview(self):
        if getattr(self, '_text_prev_id', None):
            try:
                self.root.after_cancel(self._text_prev_id)
            except Exception:
                pass
        self._text_prev_id = self.root.after(16, self._text_size_preview)

    def _text_size_preview(self):
        self._text_prev_id = None
        if getattr(self, "_multi_drag", False) or getattr(self, "_text_entry", None):
            self.canvas.delete("text_size_preview")
            return
        obj = self.selected_obj
        if not obj or obj.get('type') not in ('text', 'textbox'):
            return
        if obj.get("_drag_hide") or obj.get("_edit_hide"):
            self.canvas.delete("text_size_preview")
            return
        self.canvas.delete("text_size_preview")
        try:
            sc = self._vs()
            cx = self.img_x + self.pan_x + float(obj.get('x1', 0)) * sc
            cy = self.img_y + self.pan_y + float(obj.get('y1', 0)) * sc
            fs = max(8, min(96, int(round(obj.get('size', 24) * min(sc, 2.0)))))
            col = obj.get('color') or self.outline_color
            self.canvas.create_text(
                cx, cy, text=str(obj.get('text', '')),
                fill=col, font=("Segoe UI", fs), anchor="nw",
                tags="text_size_preview",
            )
        except Exception:
            pass

    def _prop_redraw(self):
        self._prop_after_id = None
        self.canvas.delete("text_size_preview")
        self.invalidate_cache()
        self.redraw()

    # --- PERFORMANS ÇİZİM MOTORU ---
    def to_real_coords(self, cx, cy):
        # Görüntülenen bitmap ölçeği (cap uygulanmış olabilir)
        vs = getattr(self, '_view_scale', None) or self.scale
        if vs <= 0:
            vs = self.scale
        return (cx - self.img_x - self.pan_x) / vs, (cy - self.img_y - self.pan_y) / vs

    def _vs(self):
        """Ekrandaki bitmap ölçeği"""
        vs = getattr(self, '_view_scale', None) or self.scale
        return vs if vs > 0 else self.scale


    def _scale_objects_uniform(self, objs, bases, handle, rx, ry):
        """Grup/çoklu seçim: tutamaç sürüklerken hepsini birlikte ölçekle."""
        if not objs or not bases:
            return
        # birleşik bbox (başlangıç)
        boxes = []
        for o in objs:
            b = bases.get(id(o))
            if not b:
                continue
            if b.get("points"):
                xs = [p[0] for p in b["points"]]
                ys = [p[1] for p in b["points"]]
                boxes.append((min(xs), min(ys), max(xs), max(ys)))
            else:
                x1, y1 = float(b.get("x1", 0)), float(b.get("y1", 0))
                x2 = float(b.get("x2", x1))
                y2 = float(b.get("y2", y1))
                boxes.append((min(x1, x2), min(y1, y2), max(x1, x2), max(y1, y2)))
        if not boxes:
            return
        gx1 = min(b[0] for b in boxes)
        gy1 = min(b[1] for b in boxes)
        gx2 = max(b[2] for b in boxes)
        gy2 = max(b[3] for b in boxes)
        ow = max(gx2 - gx1, 1e-6)
        oh = max(gy2 - gy1, 1e-6)
        h = handle or "se"
        # sabit köşe
        if h == "nw":
            ax, ay = gx2, gy2
            sx = (ax - rx) / ow
            sy = (ay - ry) / oh
        elif h == "ne":
            ax, ay = gx1, gy2
            sx = (rx - ax) / ow
            sy = (ay - ry) / oh
        elif h == "sw":
            ax, ay = gx2, gy1
            sx = (ax - rx) / ow
            sy = (ry - ay) / oh
        else:  # se + diğer
            ax, ay = gx1, gy1
            sx = (rx - ax) / ow
            sy = (ry - ay) / oh
        # aşırı küçük engel
        sx = max(0.05, sx)
        sy = max(0.05, sy)
        # Shift: eşit ölçek
        try:
            if self._shift_held(getattr(self, "_last_event", None) or type("E", (), {"state": 0})()):
                s = max(sx, sy)
                sx = sy = s
        except Exception:
            pass

        def xf(x, y):
            return ax + (x - ax) * sx, ay + (y - ay) * sy

        for o in objs:
            b = bases.get(id(o))
            if not b:
                continue
            if b.get("points"):
                o["points"] = [xf(p[0], p[1]) for p in b["points"]]
                xs = [p[0] for p in o["points"]]
                ys = [p[1] for p in o["points"]]
                o["x1"], o["y1"] = min(xs), min(ys)
                o["x2"], o["y2"] = max(xs), max(ys)
            else:
                x1, y1 = float(b.get("x1", 0)), float(b.get("y1", 0))
                x2 = float(b.get("x2", x1))
                y2 = float(b.get("y2", y1))
                nx1, ny1 = xf(x1, y1)
                nx2, ny2 = xf(x2, y2)
                o["x1"], o["y1"] = nx1, ny1
                if "x2" in b or o.get("type") not in ("text", "textbox"):
                    o["x2"], o["y2"] = nx2, ny2
                # metin: font boyutunu da ölçekle
                if o.get("type") in ("text", "textbox") and "size" in b:
                    o["size"] = max(8, int(round(float(b["size"]) * (abs(sx) + abs(sy)) / 2)))
                elif o.get("type") in ("text", "textbox"):
                    osz = float(o.get("size", 24) or 24)
                    o["size"] = max(8, int(round(osz * (abs(sx) + abs(sy)) / 2)))

    def _snapshot_obj_pos(self, obj):
        """Sürükleme başlangıç konumu (snap'ten bağımsız ham kopya)."""
        if obj is None:
            return {}
        snap = {'type': obj.get('type')}
        if obj.get('type') in ('pen', 'curve', 'arrow') and obj.get('points') is not None:
            snap['points'] = list(obj.get('points', []))
            snap['x1'] = obj.get('x1', 0)
            snap['y1'] = obj.get('y1', 0)
            if 'x2' in obj:
                snap['x2'] = obj['x2']
                snap['y2'] = obj['y2']
        else:
            snap['x1'] = obj.get('x1', 0)
            snap['y1'] = obj.get('y1', 0)
            if 'x2' in obj:
                snap['x2'] = obj['x2']
                snap['y2'] = obj['y2']
        if obj.get('type') in ('text', 'textbox'):
            snap['size'] = obj.get('size', 24)
        if obj.get('width') is not None:
            snap['width'] = obj.get('width')
        return snap

    def _obj_bbox(self, obj):
        """Nesne sınır kutusu (sayfa koordinatı)."""
        t = obj.get('type')
        if t in ('pen', 'curve') and obj.get('points'):
            xs = [p[0] for p in obj['points']]
            ys = [p[1] for p in obj['points']]
            return min(xs), min(ys), max(xs), max(ys)
        if t in ('text', 'textbox'):
            x1, y1 = obj.get('x1', 0), obj.get('y1', 0)
            fs = obj.get('size', 24)
            tw = fs * len(str(obj.get('text', ''))) * 0.6
            th = fs + 5
            return x1, y1, x1 + tw, y1 + th
        x1 = obj.get('x1', 0)
        y1 = obj.get('y1', 0)
        x2 = obj.get('x2', x1)
        y2 = obj.get('y2', y1)
        return min(x1, x2), min(y1, y2), max(x1, x2), max(y1, y2)

    def _clear_guides(self):
        for item in getattr(self, '_guide_items', []) or []:
            try:
                self.canvas.delete(item)
            except Exception:
                pass
        self._guide_items = []
        self.canvas.delete("snap_guide")

    def _draw_guides(self, v_lines, h_lines):
        """Ekranda hizalama kılavuz çizgileri."""
        self._clear_guides()
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        color = getattr(self, "snap_guide_color", None) or "#00e5ff"
        for x in v_lines:
            sx = self.img_x + self.pan_x + x * self._vs()
            iid = self.canvas.create_line(
                sx, 0, sx, ch, fill=color, width=1, dash=(4, 3), tags="snap_guide"
            )
            self._guide_items.append(iid)
        for y in h_lines:
            sy = self.img_y + self.pan_y + y * self._vs()
            iid = self.canvas.create_line(
                0, sy, cw, sy, fill=color, width=1, dash=(4, 3), tags="snap_guide"
            )
            self._guide_items.append(iid)


    def _snap_resize_edges(self, obj, handle):
        """Boyutlandırırken kenarları diğer nesnelere ve sayfaya yapıştır."""
        if not obj or not self.original_image:
            return
        thr = self.snap_threshold_px / max(self._vs(), 1e-6)
        pw, ph = self.original_image.size
        anchors_x = [0.0, float(pw)]
        anchors_y = [0.0, float(ph)]
        for o in self.objects:
            if o is obj or self._is_locked(o):
                continue
            try:
                if o.get("points"):
                    xs = [p[0] for p in o["points"]]
                    ys = [p[1] for p in o["points"]]
                    anchors_x.extend([min(xs), max(xs)])
                    anchors_y.extend([min(ys), max(ys)])
                else:
                    x1, y1 = float(o.get("x1", 0)), float(o.get("y1", 0))
                    x2, y2 = float(o.get("x2", x1)), float(o.get("y2", y1))
                    anchors_x.extend([min(x1, x2), max(x1, x2)])
                    anchors_y.extend([min(y1, y2), max(y1, y2)])
            except Exception:
                continue

        def near(v, anchors):
            best, bd = v, thr
            for a in anchors:
                d = abs(v - a)
                if d < bd:
                    best, bd = a, d
            return best

        h = handle or ""
        gx, gy = [], []
        if "w" in h or h == "nw" or h == "sw":
            obj["x1"] = near(float(obj.get("x1", 0)), anchors_x)
            gx.append(obj["x1"])
        if "e" in h or h == "ne" or h == "se":
            obj["x2"] = near(float(obj.get("x2", 0)), anchors_x)
            gx.append(obj["x2"])
        if "n" in h or h == "nw" or h == "ne":
            obj["y1"] = near(float(obj.get("y1", 0)), anchors_y)
            gy.append(obj["y1"])
        if "s" in h or h == "sw" or h == "se":
            obj["y2"] = near(float(obj.get("y2", 0)), anchors_y)
            gy.append(obj["y2"])
        try:
            self._draw_guides(gx, gy)
        except Exception:
            pass

    def _snap_group_bbox(self, objs, handle):
        """Çoklu/grup seçimde birleşik kutuyu kenar snap ile hizala."""
        if not objs or not self.original_image:
            return
        thr = self.snap_threshold_px / max(self._vs(), 1e-6)
        pw, ph = self.original_image.size
        # mevcut birleşik bbox
        boxes = []
        for o in objs:
            try:
                if o.get("points"):
                    xs = [p[0] for p in o["points"]]
                    ys = [p[1] for p in o["points"]]
                    boxes.append((min(xs), min(ys), max(xs), max(ys)))
                else:
                    x1, y1 = float(o.get("x1", 0)), float(o.get("y1", 0))
                    x2, y2 = float(o.get("x2", x1)), float(o.get("y2", y1))
                    boxes.append((min(x1, x2), min(y1, y2), max(x1, x2), max(y1, y2)))
            except Exception:
                continue
        if not boxes:
            return
        gx1 = min(b[0] for b in boxes)
        gy1 = min(b[1] for b in boxes)
        gx2 = max(b[2] for b in boxes)
        gy2 = max(b[3] for b in boxes)
        anchors_x = [0.0, float(pw)]
        anchors_y = [0.0, float(ph)]
        for o in self.objects:
            if o in objs:
                continue
            try:
                if o.get("points"):
                    xs = [p[0] for p in o["points"]]
                    ys = [p[1] for p in o["points"]]
                    anchors_x.extend([min(xs), max(xs)])
                    anchors_y.extend([min(ys), max(ys)])
                else:
                    x1, y1 = float(o.get("x1", 0)), float(o.get("y1", 0))
                    x2, y2 = float(o.get("x2", x1)), float(o.get("y2", y1))
                    anchors_x.extend([min(x1, x2), max(x1, x2)])
                    anchors_y.extend([min(y1, y2), max(y1, y2)])
            except Exception:
                continue

        def near(v, anchors):
            best, bd = v, thr
            for a in anchors:
                d = abs(v - a)
                if d < bd:
                    best, bd = a, d
            return best

        dx = dy = 0.0
        h = handle or ""
        if "w" in h or h == "nw" or h == "sw":
            nx = near(gx1, anchors_x)
            dx = nx - gx1
        if "e" in h or h == "ne" or h == "se":
            nx = near(gx2, anchors_x)
            dx = nx - gx2
        if "n" in h or h == "nw" or h == "ne":
            ny = near(gy1, anchors_y)
            dy = ny - gy1
        if "s" in h or h == "sw" or h == "se":
            ny = near(gy2, anchors_y)
            dy = ny - gy2
        if abs(dx) < 1e-9 and abs(dy) < 1e-9:
            return
        for o in objs:
            if o.get("points"):
                o["points"] = [(p[0] + dx, p[1] + dy) for p in o["points"]]
            o["x1"] = o.get("x1", 0) + dx
            o["y1"] = o.get("y1", 0) + dy
            if "x2" in o:
                o["x2"] = o.get("x2", 0) + dx
                o["y2"] = o.get("y2", 0) + dy
        try:
            self._draw_guides(
                [gx1 + dx if ("w" in h or h in ("nw", "sw")) else (gx2 + dx if ("e" in h or h in ("ne", "se")) else None)],
                [gy1 + dy if ("n" in h or h in ("nw", "ne")) else (gy2 + dy if ("s" in h or h in ("sw", "se")) else None)],
            )
        except Exception:
            pass

    def _snap_move(self, obj):

        """Ham konumdan snap uygula. Eşik dışına çıkınca serbest bırakır (takılmaz)."""
        if not obj:
            self._clear_guides()
            return 0.0, 0.0

        thr = self.snap_threshold_px / max(self._vs(), 1e-6)
        # grup / çoklu seçimde birleşik kutu
        sel = [o for o in (self.selected_objs or []) if o is not None]
        if len(sel) > 1:
            boxes = []
            for o in sel:
                try:
                    boxes.append(self._obj_bbox(o))
                except Exception:
                    pass
            if boxes:
                l = min(b[0] for b in boxes)
                t = min(b[1] for b in boxes)
                r = max(b[2] for b in boxes)
                b = max(b[3] for b in boxes)
            else:
                l, t, r, b = self._obj_bbox(obj)
        else:
            l, t, r, b = self._obj_bbox(obj)
        cx, cy = (l + r) / 2.0, (t + b) / 2.0

        targets_x = []
        targets_y = []
        pw, ph = self.original_image.size
        targets_x.extend([0.0, pw / 2.0, float(pw)])
        targets_y.extend([0.0, ph / 2.0, float(ph)])

        exclude = set()
        if obj is not None:
            exclude.add(id(obj))
            for m in self._group_members(obj):
                exclude.add(id(m))
        for o in (self.selected_objs or []):
            if o is not None:
                exclude.add(id(o))
                for m in self._group_members(o):
                    exclude.add(id(m))

        for other in self.objects:
            if id(other) in exclude:
                continue
            try:
                ol, ot, orr, ob = self._obj_bbox(other)
            except Exception:
                continue
            targets_x.extend([ol, (ol + orr) / 2.0, orr])
            targets_y.extend([ot, (ot + ob) / 2.0, ob])

        dx_snap = 0.0
        best_dx = thr + 1.0
        guide_xs = []
        for val in (l, cx, r):
            for tx in targets_x:
                d = tx - val
                ad = abs(d)
                if ad <= thr and ad < best_dx:
                    best_dx = ad
                    dx_snap = d
                    guide_xs = [tx]

        dy_snap = 0.0
        best_dy = thr + 1.0
        guide_ys = []
        for val in (t, cy, b):
            for ty in targets_y:
                d = ty - val
                ad = abs(d)
                if ad <= thr and ad < best_dy:
                    best_dy = ad
                    dy_snap = d
                    guide_ys = [ty]

        # Ek kılavuzlar (aynı hizada birden fazla kenar)
        if dx_snap != 0.0 or best_dx <= thr:
            gx = []
            for val in (l + dx_snap, cx + dx_snap, r + dx_snap):
                for tx in targets_x:
                    if abs(tx - val) <= 0.51:
                        gx.append(tx)
            guide_xs = list(dict.fromkeys(gx)) if gx else guide_xs
        if dy_snap != 0.0 or best_dy <= thr:
            gy = []
            for val in (t + dy_snap, cy + dy_snap, b + dy_snap):
                for ty in targets_y:
                    if abs(ty - val) <= 0.51:
                        gy.append(ty)
            guide_ys = list(dict.fromkeys(gy)) if gy else guide_ys

        if guide_xs or guide_ys:
            self._draw_guides(guide_xs, guide_ys)
        else:
            self._clear_guides()

        return dx_snap, dy_snap



    def _font_candidates(self):
        return [
            "segoeui.ttf", "SegoeUI.ttf", "arial.ttf", "Arial.ttf",
            "DejaVuSans.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
            "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
            "/usr/share/fonts/truetype/freefont/FreeSans.ttf",
            "C:\\Windows\\Fonts\\segoeui.ttf",
            "C:\\Windows\\Fonts\\arial.ttf",
        ]

    def _load_label_font(self, size):
        size = max(6, int(size))
        cache = getattr(self, "_font_cache", None)
        if cache is None:
            self._font_cache = {}
            cache = self._font_cache
        if size in cache:
            return cache[size]
        font = None
        for path in self._font_candidates():
            try:
                font = ImageFont.truetype(path, size)
                break
            except Exception:
                continue
        if font is None:
            font = ImageFont.load_default()
        cache[size] = font
        return font

    def _draw_text_with_bg(self, result, obj, x1, y1, sc, outline_rgba):
        """Metin + arka plan: BG yalnızca metin kutusunu doldurur (taşmaz)."""
        text = obj.get("text") or ""
        if not text:
            return result
        size = float(obj.get("size", 24)) * sc
        bg = obj.get("bg_color") or ""
        op = obj.get("opacity", 100)
        lines = text.split(chr(10))
        line_gap = size * 1.15
        font = self._load_label_font(max(6, int(round(size))))
        probe = Image.new("RGBA", (8, 8), (0, 0, 0, 0))
        pd = ImageDraw.Draw(probe)
        widths, heights = [], []
        for ln in lines:
            try:
                bb = pd.textbbox((0, 0), ln if ln else " ", font=font)
            except Exception:
                bb = (0, 0, max(8, len(ln or " ") * int(size * 0.55)), int(size))
            widths.append(max(1, bb[2] - bb[0]))
            heights.append(max(1, bb[3] - bb[1]))
        max_w = max(widths) if widths else int(size)
        # satır yüksekliği tutarlı (font bbox + gap)
        total_h = 0
        for i, h in enumerate(heights):
            total_h += h
            if i < len(heights) - 1:
                total_h += max(0, line_gap - h) * 0.15 + max(2, int(size * 0.08))
        # daha doğru: sabit satır adımı
        total_h = int(round(line_gap * max(1, len(lines) - 1) + (heights[-1] if heights else size)))
        max_w = int(max_w)
        total_h = max(int(heights[0] if heights else size), int(total_h))
        # sıkı pad — sadece metin kutusu
        pad_x = max(3, int(round(size * 0.12)))
        pad_y = max(2, int(round(size * 0.08)))

        if bg:
            bg_rgba = self.hex_to_rgba(bg, op)
            box = Image.new("RGBA", result.size, (0, 0, 0, 0))
            bd = ImageDraw.Draw(box)
            left = int(round(x1 - pad_x))
            top = int(round(y1 - pad_y))
            right = int(round(x1 + max_w + pad_x))
            bottom = int(round(y1 + total_h + pad_y))
            bd.rectangle([left, top, right, bottom], fill=bg_rgba)
            result = Image.alpha_composite(result, box)

        # satır satır çiz
        y = y1
        for i, ln in enumerate(lines):
            result = self._paste_text_hq(result, ln, x1, y, size, outline_rgba, sc=1.0)
            y += line_gap
        return result


    def _paste_text_hq(self, result, text, x, y, size, fill_rgba, sc=1.0):
        """Supersampled metin — daha keskin, daha az pürüz.\n        result: RGBA Image; x,y ölçeklenmiş ekran koordinatı.\n        """
        text = text if text is not None else ""
        if not text:
            return result
        try:
            pixel_size = max(6, int(round(size * sc)))
        except Exception:
            pixel_size = max(6, int(size))
        # 2x supersample (çok büyükse 1x — kasma olmasın)
        ss = 2 if pixel_size * max(1, len(text)) < 1200 else 1
        font = self._load_label_font(max(6, pixel_size * ss))
        # ölçü
        probe = Image.new("RGBA", (8, 8), (0, 0, 0, 0))
        pd = ImageDraw.Draw(probe)
        try:
            bb = pd.textbbox((0, 0), text, font=font)
        except Exception:
            bb = (0, 0, max(8, len(text) * pixel_size), pixel_size)
        tw = max(1, bb[2] - bb[0])
        th = max(1, bb[3] - bb[1])
        pad = 4 * ss
        tile = Image.new("RGBA", (tw + pad * 2, th + pad * 2), (0, 0, 0, 0))
        td = ImageDraw.Draw(tile)
        # fill_rgba may be tuple
        if isinstance(fill_rgba, str):
            fill_rgba = self.hex_to_rgba(fill_rgba, 100)
        try:
            td.text((pad - bb[0], pad - bb[1]), text, font=font, fill=fill_rgba)
        except Exception:
            td.text((pad, pad), text, font=font, fill=fill_rgba or (0, 0, 0, 255))
        if ss > 1:
            out_w = max(1, int(round((tw + pad * 2) / ss)))
            out_h = max(1, int(round((th + pad * 2) / ss)))
            tile = tile.resize((out_w, out_h), Image.Resampling.LANCZOS)
            ox = int(round(x - pad / ss))
            oy = int(round(y - pad / ss))
        else:
            ox = int(round(x - pad))
            oy = int(round(y - pad))
        # paste with alpha
        try:
            if result.mode != "RGBA":
                result = result.convert("RGBA")
            # clip paste
            layer = Image.new("RGBA", result.size, (0, 0, 0, 0))
            layer.paste(tile, (ox, oy), tile)
            result = Image.alpha_composite(result, layer)
        except Exception:
            pass
        return result

    def _text_size(self, draw, text, font):
        try:
            bb = draw.textbbox((0, 0), text, font=font)
            return bb[2] - bb[0], bb[3] - bb[1]
        except Exception:
            try:
                return font.getsize(text)
            except Exception:
                return max(1, len(text) * 6), 12

    def _wrap_text_lines(self, draw, text, font, max_width):
        """Kelime bazlı satır kaydırma; tek kelime sığmazsa karakter kır."""
        text = (text or "").strip()
        if not text:
            return []
        max_width = max(4, max_width)
        words = text.split()
        lines = []
        cur = ""
        for word in words:
            trial = word if not cur else cur + " " + word
            tw, _ = self._text_size(draw, trial, font)
            if tw <= max_width:
                cur = trial
                continue
            if cur:
                lines.append(cur)
            wtw, _ = self._text_size(draw, word, font)
            if wtw <= max_width:
                cur = word
            else:
                piece = ""
                for ch in word:
                    t2 = piece + ch
                    cw, _ = self._text_size(draw, t2, font)
                    if cw <= max_width or not piece:
                        piece = t2
                    else:
                        lines.append(piece)
                        piece = ch
                cur = piece
        if cur:
            lines.append(cur)
        return lines

    def _fit_label_layout(self, draw, text, box_w, box_h, preferred_size, pad_ratio=0.08):
        """Şekil kutusuna sığan font + satırlar (binary search — hızlı)."""
        text = (text or "").strip()
        if not text or box_w < 4 or box_h < 4:
            return None, [], 0, 0
        # çok küçük kutu: tek satır min font
        if box_w < 18 or box_h < 14:
            font = self._load_label_font(6)
            return font, [text[:8] + ("…" if len(text) > 8 else "")], 8, 8

        pad_x = max(2, box_w * pad_ratio)
        pad_y = max(2, box_h * pad_ratio)
        usable_w = max(4, box_w - 2 * pad_x)
        usable_h = max(4, box_h - 2 * pad_y)
        max_size = max(6, min(int(preferred_size), 120))
        min_size = 6

        def try_size(size):
            font = self._load_label_font(size)
            lines = self._wrap_text_lines(draw, text, font, usable_w)
            if not lines:
                return False, font, [], 0, 0
            _, sample_h = self._text_size(draw, "Ag", font)
            line_h = max(sample_h, size) + max(1, size // 6)
            total_h = line_h * len(lines)
            if total_h > usable_h:
                return False, font, lines, line_h, total_h
            for ln in lines:
                tw, _ = self._text_size(draw, ln, font)
                if tw > usable_w + 1:
                    return False, font, lines, line_h, total_h
            return True, font, lines, line_h, total_h

        lo, hi = min_size, max_size
        best = None
        while lo <= hi:
            mid = (lo + hi) // 2
            ok, font, lines, line_h, total_h = try_size(mid)
            if ok:
                best = (font, lines, line_h, total_h)
                lo = mid + 1
            else:
                hi = mid - 1
                if best is None:
                    best = (font, lines, line_h, total_h)
        if best is None:
            font = self._load_label_font(min_size)
            lines = self._wrap_text_lines(draw, text, font, usable_w)
            _, sample_h = self._text_size(draw, "Ag", font)
            line_h = max(sample_h, min_size) + 1
            return font, lines, line_h, line_h * max(1, len(lines))
        return best

    def _draw_shape_label(self, draw, obj, x1, y1, x2, y2, sc, opacity=None):
        """Şekil içinde ortalanmış, otomatik sığdırılmış çok satırlı etiket."""
        text = obj.get("label")
        if not text:
            return
        box_w = abs(x2 - x1)
        box_h = abs(y2 - y1)
        preferred = max(6, int(obj.get("label_size", 18) * (sc if sc else 1)))
        # sc zaten koordinatlara uygulanmışsa preferred_size de sc ile ölçekli gelir
        font, lines, line_h, total_h = self._fit_label_layout(
            draw, text, box_w, box_h, preferred
        )
        if not lines:
            return
        op = opacity if opacity is not None else obj.get("opacity", 100)
        lc = self.hex_to_rgba(
            obj.get("label_color") or obj.get("color") or "#000000", op
        )
        cx = (x1 + x2) / 2
        cy = (y1 + y2) / 2
        y = cy - total_h / 2
        for ln in lines:
            tw, th = self._text_size(draw, ln, font)
            draw.text((cx - tw / 2, y + (line_h - th) / 2), ln, fill=lc, font=font)
            y += line_h

    def hex_to_rgba(self, hex_code, opacity_percent):

        """Hex renk kodunu RGBA'ya çevirir - ŞEFFAFLIK DÜZELTİLDİ"""
        if not hex_code:
            return (0, 0, 0, 0)
        
        hex_code = hex_code.lstrip('#')
        
        # 3 haneli hex ise (örn: #fff) 6 haneli yap
        if len(hex_code) == 3:
            hex_code = ''.join([c*2 for c in hex_code])
        
        # RGB değerlerini al
        try:
            rgb = tuple(int(hex_code[i:i + 2], 16) for i in (0, 2, 4))
        except ValueError:
            return (255, 0, 0, 255)  # Hata durumunda kırmızı
        
        # Alpha değerini hesapla (0-255 arası)
        alpha = int(255 * (opacity_percent / 100.0))
        alpha = max(0, min(255, alpha))
        
        return (rgb[0], rgb[1], rgb[2], alpha)

    def get_scaled_bg(self):
        """Arka planı self.scale ile birebir ölçekle (sıçrama olmasın)."""
        sc = self.scale
        # Sürüklerken aşırı yakın zoom'da render boyutunu sınırla (kasma)
        if getattr(self, "_multi_drag", False) and sc > 2.5:
            sc = 2.5
        if self.cached_scale == sc and self.cached_bg is not None:
            return self.cached_bg

        new_w = max(1, int(round(self.original_image.width * sc)))
        new_h = max(1, int(round(self.original_image.height * sc)))
        # Çok büyük yüzeyleri sınırla
        max_px = 6_000_000
        if new_w * new_h > max_px:
            f = (max_px / (new_w * new_h)) ** 0.5
            new_w = max(1, int(new_w * f))
            new_h = max(1, int(new_h * f))
        self.cached_bg = self.original_image.resize((new_w, new_h), Image.Resampling.BILINEAR)
        self.cached_scale = sc
        self._render_sx = sc
        self._render_sy = sc
        return self.cached_bg


    def _rotate_points(self, points, cx, cy, degrees):
        if not degrees:
            return list(points)
        a = math.radians(degrees)
        cos_a, sin_a = math.cos(a), math.sin(a)
        out = []
        for x, y in points:
            dx, dy = x - cx, y - cy
            out.append((cx + dx * cos_a - dy * sin_a, cy + dx * sin_a + dy * cos_a))
        return out

    def _shape_points(self, obj, x1, y1, x2, y2):
        """Şekil köşe noktaları (ekran/ölçekli koordinat). flip + rotation uygulanır."""
        t = obj.get("type")
        l, r = min(x1, x2), max(x1, x2)
        top, bot = min(y1, y2), max(y1, y2)
        w, h = max(1e-6, r - l), max(1e-6, bot - top)
        cx, cy = (l + r) / 2, (top + bot) / 2
        pts = []
        if t in ("rect", "square"):
            pts = [(l, top), (r, top), (r, bot), (l, bot)]
        elif t == "circle":
            n = 48
            for i in range(n):
                ang = 2 * math.pi * i / n
                pts.append((cx + (w / 2) * math.cos(ang), cy + (h / 2) * math.sin(ang)))
        elif t == "triangle":
            pts = [(cx, top), (l, bot), (r, bot)]
        elif t == "hexagon":
            for i in range(6):
                ang = math.radians(60 * i - 30)
                pts.append((cx + (w / 2) * math.cos(ang), cy + (h / 2) * math.sin(ang)))
        elif t == "star":
            for i in range(10):
                ang = math.radians(-90 + i * 36)
                rad = (w / 2 if i % 2 == 0 else w / 4, h / 2 if i % 2 == 0 else h / 4)
                pts.append((cx + rad[0] * math.cos(ang), cy + rad[1] * math.sin(ang)))
        elif t == "callout":
            body_b = top + h * 0.72
            pts = [
                (l, top), (r, top), (r, body_b),
                (l + w * 0.55, body_b), (l + w * 0.35, bot), (l + w * 0.45, body_b),
                (l, body_b),
            ]
        # Ayna (geometri)
        if obj.get("flip_h"):
            pts = [(2 * cx - x, y) for x, y in pts]
        if obj.get("flip_v"):
            pts = [(x, 2 * cy - y) for x, y in pts]
        rot = obj.get("rotation", 0) or 0
        if rot:
            pts = self._rotate_points(pts, cx, cy, rot)
        return pts

    def render_preview(self, exclude_selected=False):
        """Tüm çizimleri ekrana render et - z-order + üst üste şeffaflık doğru"""
        bg = self.get_scaled_bg()
        if bg.mode != "RGBA":
            bg = bg.convert("RGBA")
        else:
            bg = bg.copy()

        result = bg
        visible_layers = [l["id"] for l in self.layers if l["visible"]]
        sc = self.scale

        def draw_shape(draw, obj, outline_rgba, fill_rgba, x1, y1, x2, y2, w, sc):
            t = obj['type']
            if t in ('text', 'textbox'):
                return  # HQ metin ana döngüde _paste_text_hq ile
            elif t == 'circle' and not obj.get('rotation') and not obj.get('flip_h') and not obj.get('flip_v'):
                draw.ellipse([x1, y1, x2, y2], outline=outline_rgba, fill=fill_rgba, width=w)
            elif t in ('rect', 'square', 'circle', 'triangle', 'hexagon', 'star', 'callout'):
                pts = self._shape_points(obj, x1, y1, x2, y2)
                if len(pts) >= 3:
                    draw.polygon(pts, outline=outline_rgba, fill=fill_rgba, width=w)
            elif t == 'arrow':
                pts = obj.get('points')
                if pts and len(pts) >= 2:
                    scaled = [(p[0] * sc, p[1] * sc) for p in pts]
                    draw.line(scaled, fill=outline_rgba, width=w, joint="curve")
                    x1, y1 = scaled[-2]
                    x2, y2 = scaled[-1]
                else:
                    draw.line([x1, y1, x2, y2], fill=outline_rgba, width=w)
                angle = math.atan2(y2 - y1, x2 - x1)
                al, aa = w * 3 + 10, math.pi / 6
                draw.polygon([
                    x2, y2,
                    x2 - al * math.cos(angle - aa),
                    y2 - al * math.sin(angle - aa),
                    x2 - al * math.cos(angle + aa),
                    y2 - al * math.sin(angle + aa)
                ], fill=outline_rgba)
            elif t == 'curve' and len(obj.get('points', [])) >= 2:
                scaled = [(p[0] * sc, p[1] * sc) for p in obj['points']]
                if len(scaled) == 2:
                    draw.line(scaled, fill=outline_rgba, width=w)
                else:
                    # quadratic approx: dense samples
                    p0, p1, p2 = scaled[0], scaled[1], scaled[2] if len(scaled) > 2 else scaled[1]
                    samples = []
                    for i in range(33):
                        tt = i / 32
                        ax = (1 - tt) * (1 - tt) * p0[0] + 2 * (1 - tt) * tt * p1[0] + tt * tt * p2[0]
                        ay = (1 - tt) * (1 - tt) * p0[1] + 2 * (1 - tt) * tt * p1[1] + tt * tt * p2[1]
                        samples.append((ax, ay))
                    draw.line(samples, fill=outline_rgba, width=w, joint="curve")
            elif t == 'pen' and len(obj.get('points', [])) > 1:
                scaled_pts = [(px * sc, py * sc) for px, py in obj['points']]
                draw.line(scaled_pts, fill=outline_rgba, width=w, joint="curve")
            # Şekil etiketi: otomatik sığdır + satır kaydır + ortala
            if obj.get('label') and t not in ('text', 'pen', 'arrow', 'curve'):
                try:
                    self._draw_shape_label(draw, obj, x1, y1, x2, y2, sc)
                except Exception:
                    pass

        # Ardışık opak nesneleri tek katmanda topla (hız), şeffaf olunca flush
        batch = Image.new("RGBA", result.size, (0, 0, 0, 0))
        batch_draw = ImageDraw.Draw(batch, "RGBA")
        batch_used = False

        def flush_batch():
            nonlocal result, batch, batch_draw, batch_used
            if batch_used:
                result = Image.alpha_composite(result, batch)
                batch = Image.new("RGBA", result.size, (0, 0, 0, 0))
                batch_draw = ImageDraw.Draw(batch, "RGBA")
                batch_used = False

        for obj in self.objects:
            # Sürükleme sırasında gizle (üst üste yazı/şekil hayaleti önler)
            if obj.get("_drag_hide") or obj.get("_edit_hide"):
                continue
            if exclude_selected:
                sel = list(getattr(self, "selected_objs", None) or [])
                if self.selected_obj and self.selected_obj not in sel:
                    sel.append(self.selected_obj)
                if any(obj is s for s in sel):
                    continue
            if obj.get('layer', 0) not in visible_layers:
                continue

            op = obj.get('opacity', 100)
            outline_rgba = self.hex_to_rgba(obj.get('color') or '#000000', op)
            fill_rgba = self.hex_to_rgba(obj.get('fill'), op) if obj.get('fill') else None
            x1 = obj.get('x1', 0) * sc
            y1 = obj.get('y1', 0) * sc
            x2 = obj.get('x2', 0) * sc
            y2 = obj.get('y2', 0) * sc
            w = max(1, int(obj.get('width', 1) * sc))

            if obj['type'] in ('text', 'textbox'):
                flush_batch()
                result = self._draw_text_with_bg(result, obj, x1, y1, sc, outline_rgba)
                continue

            if obj['type'] in ('image', 'fill_region') and obj.get('pil_image') is not None:
                flush_batch()
                layer = Image.new("RGBA", result.size, (0, 0, 0, 0))
                try:
                    iw = max(1, int(abs(x2 - x1)))
                    ih = max(1, int(abs(y2 - y1)))
                    cache = obj.get('_rz_cache')
                    rot = obj.get('rotation', 0) or 0
                    if cache and cache[0] == iw and cache[1] == ih and cache[3] == op and (len(cache) < 5 or cache[4] == rot):
                        resized = cache[2]
                    else:
                        base_img = obj['pil_image']
                        rot = obj.get('rotation', 0) or 0
                        if rot:
                            base_img = base_img.rotate(-rot, expand=True, resample=Image.Resampling.BILINEAR)
                        resized = base_img.resize((iw, ih), Image.Resampling.BILINEAR)
                        if resized.mode != 'RGBA':
                            resized = resized.convert('RGBA')
                        if op < 100:
                            alpha = resized.split()[-1]
                            alpha = alpha.point(lambda a, o=op: int(a * o / 100.0))
                            resized.putalpha(alpha)
                        obj['_rz_cache'] = (iw, ih, resized, op, rot)
                    px, py = int(min(x1, x2)), int(min(y1, y2))
                    layer.paste(resized, (px, py), resized)
                except Exception:
                    pass
                result = Image.alpha_composite(result, layer)
                continue

            if op >= 100:
                draw_shape(batch_draw, obj, outline_rgba, fill_rgba, x1, y1, x2, y2, w, sc)
                batch_used = True
            else:
                flush_batch()
                layer = Image.new("RGBA", result.size, (0, 0, 0, 0))
                draw = ImageDraw.Draw(layer, "RGBA")
                draw_shape(draw, obj, outline_rgba, fill_rgba, x1, y1, x2, y2, w, sc)
                result = Image.alpha_composite(result, layer)

        flush_batch()
        return result


    def draw_selection_ui(self):
        """Seçim kutularını ve tutamaçları çiz"""
        self.canvas.delete("movable")
        self.canvas.delete("locked_item")
        self.canvas.delete("selection_ui")
        self.handle_rects = []
        visible_layers = [l["id"] for l in self.layers if l["visible"]]
        sc = self._vs()

        def _hit_tag(o):
            # kilitli → movable DEĞİL (sürüklenemez)
            return "locked_item" if self._is_locked(o) else "movable"

        for obj in self.objects:
            if obj.get('layer', 0) not in visible_layers:
                continue
            
            cx1 = self.img_x + self.pan_x + (obj.get('x1', 0) * sc)
            cy1 = self.img_y + self.pan_y + (obj.get('y1', 0) * sc)
            tag = _hit_tag(obj)
            
            if obj['type'] in ('text', 'textbox'):
                fs = max(1, int(obj.get('size', 24) * sc))
                raw = str(obj.get('text', '') or '')
                lines = raw.splitlines() or [raw]
                if not lines:
                    lines = ['']
                max_len = max((len(ln) for ln in lines), default=1)
                tw = max(fs * 2, int(fs * max_len * 0.55) + 8)
                th = max(fs + 4, int(len(lines) * fs * 1.25) + 6)
                # arka plan varsa biraz daha geniş
                if obj.get('bg_color'):
                    tw += 8
                    th += 8
                obj['id'] = self.canvas.create_rectangle(
                    cx1, cy1, cx1 + tw, cy1 + th,
                    fill="", outline="", tags=tag,
                )
                if self._is_locked(obj):
                    pass  # seçilemez — seçim çerçevesi yok
                elif obj in self.selected_objs or obj == self.selected_obj:
                    self.canvas.create_rectangle(
                        cx1-2, cy1-2, cx1+tw, cy1+th,
                        outline=self.colors["accent"], dash=(2,2), width=2, tags="selection_ui"
                    )
                    self.handle_rects.append((
                        'se',
                        self.canvas.create_rectangle(
                            cx1+tw-7, cy1+th-7, cx1+tw+7, cy1+th+7,
                            fill=self.colors["accent"], outline="white", tags="selection_ui"
                        )
                    ))
            
            elif obj['type'] in ['rect', 'square', 'circle', 'triangle', 'hexagon', 'star', 'callout', 'image', 'fill_region']:
                cx2 = self.img_x + self.pan_x + (obj['x2'] * sc)
                cy2 = self.img_y + self.pan_y + (obj['y2'] * sc)
                obj['id'] = self.canvas.create_rectangle(
                    cx1, cy1, cx2, cy2,
                    fill="", outline="", tags=tag
                )
                if obj in self.selected_objs and obj != self.selected_obj:
                    self.canvas.create_rectangle(
                        min(cx1, cx2), min(cy1, cy2), max(cx1, cx2), max(cy1, cy2),
                        outline="#00e5ff", dash=(3, 2), width=1, tags="selection_ui"
                    )
                if obj == self.selected_obj:
                    self.canvas.create_rectangle(
                        cx1, cy1, cx2, cy2,
                        outline=self.colors["accent"], dash=(2,2), width=2, tags="selection_ui"
                    )
                    self.handle_rects.append((
                        'nw',
                        self.canvas.create_rectangle(
                            cx1-7, cy1-7, cx1+7, cy1+7,
                            fill=self.colors["accent"], outline="white", tags="selection_ui"
                        )
                    ))
                    self.handle_rects.append((
                        'ne',
                        self.canvas.create_rectangle(
                            cx2-7, cy1-7, cx2+7, cy1+7,
                            fill=self.colors["accent"], outline="white", tags="selection_ui"
                        )
                    ))
                    self.handle_rects.append((
                        'sw',
                        self.canvas.create_rectangle(
                            cx1-7, cy2-7, cx1+7, cy2+7,
                            fill=self.colors["accent"], outline="white", tags="selection_ui"
                        )
                    ))
                    self.handle_rects.append((
                        'se',
                        self.canvas.create_rectangle(
                            cx2-7, cy2-7, cx2+7, cy2+7,
                            fill=self.colors["accent"], outline="white", tags="selection_ui"
                        )
                    ))

            elif obj['type'] == 'arrow':
                pts = obj.get('points')
                if pts and len(pts) >= 2:
                    xs = [self.img_x + self.pan_x + p[0] * sc for p in pts]
                    ys = [self.img_y + self.pan_y + p[1] * sc for p in pts]
                    pad = max(12, int(obj.get('width', 3) * sc) + 8)
                    min_x, max_x = min(xs) - pad, max(xs) + pad
                    min_y, max_y = min(ys) - pad, max(ys) + pad
                    obj['id'] = self.canvas.create_rectangle(
                        min_x, min_y, max_x, max_y,
                        fill="", outline="", width=0, tags=_hit_tag(obj),
                    )
                    flat = []
                    for p in pts:
                        flat.extend([
                            self.img_x + self.pan_x + p[0] * sc,
                            self.img_y + self.pan_y + p[1] * sc,
                        ])
                    self.canvas.create_line(
                        *flat, fill="", width=max(14, int(obj.get('width', 3) * sc) + 10),
                        tags=_hit_tag(obj),
                    )
                    obj['x1'], obj['y1'] = min(p[0] for p in pts), min(p[1] for p in pts)
                    obj['x2'], obj['y2'] = max(p[0] for p in pts), max(p[1] for p in pts)
                    if obj in self.selected_objs or obj == self.selected_obj:
                        self.canvas.create_rectangle(
                            min_x, min_y, max_x, max_y,
                            outline=self.colors["accent"] if obj == self.selected_obj else "#00e5ff",
                            dash=(2, 2), width=2, tags="selection_ui",
                        )
                    if obj == self.selected_obj and not self._is_locked(obj):
                        for i, (px, py) in enumerate(pts):
                            hx = self.img_x + self.pan_x + px * sc
                            hy = self.img_y + self.pan_y + py * sc
                            fill_c = "#00e5ff" if 0 < i < len(pts) - 1 else self.colors["accent"]
                            hid = self.canvas.create_rectangle(
                                hx - 7, hy - 7, hx + 7, hy + 7,
                                fill=fill_c, outline="white", width=1, tags="selection_ui",
                            )
                            self.handle_rects.append((f"apt{i}", hid))
                else:
                    cx2 = self.img_x + self.pan_x + (obj.get('x2', 0) * sc)
                    cy2 = self.img_y + self.pan_y + (obj.get('y2', 0) * sc)
                    obj['id'] = self.canvas.create_line(
                        cx1, cy1, cx2, cy2,
                        fill="", width=max(12, int(obj.get('width', 3) * sc) + 8), tags=_hit_tag(obj),
                    )
                    if obj == self.selected_obj:
                        self.canvas.create_rectangle(
                            min(cx1, cx2), min(cy1, cy2),
                            max(cx1, cx2), max(cy1, cy2),
                            outline=self.colors["accent"], dash=(2, 2), width=2, tags="selection_ui",
                        )
                        if not self._is_locked(obj):
                            self.handle_rects.append((
                                "start",
                                self.canvas.create_rectangle(
                                    cx1 - 7, cy1 - 7, cx1 + 7, cy1 + 7,
                                    fill=self.colors["accent"], outline="white", tags="selection_ui",
                                ),
                            ))
                            self.handle_rects.append((
                                "end",
                                self.canvas.create_rectangle(
                                    cx2 - 7, cy2 - 7, cx2 + 7, cy2 + 7,
                                    fill=self.colors["accent"], outline="white", tags="selection_ui",
                                ),
                            ))

            elif obj['type'] in ('pen', 'curve') and len(obj.get('points', [])) > 1:
                xs = [self.img_x + self.pan_x + p[0]*sc for p in obj['points']]
                ys = [self.img_y + self.pan_y + p[1]*sc for p in obj['points']]
                pad = max(8, int(obj.get('width', 3) * sc))
                min_x, max_x = min(xs) - pad, max(xs) + pad
                min_y, max_y = min(ys) - pad, max(ys) + pad
                # Görünmez ama tıklanabilir alan
                obj['id'] = self.canvas.create_rectangle(
                    min_x, min_y, max_x, max_y,
                    fill="", outline="", width=0, tags=_hit_tag(obj)
                )
                obj['x1'], obj['y1'] = min(p[0] for p in obj['points']), min(p[1] for p in obj['points'])
                obj['x2'], obj['y2'] = max(p[0] for p in obj['points']), max(p[1] for p in obj['points'])
                if obj in self.selected_objs or obj == self.selected_obj:
                    self.canvas.create_rectangle(
                        min_x, min_y, max_x, max_y,
                        outline=self.colors["accent"] if obj == self.selected_obj else "#00e5ff",
                        dash=(2, 2), width=2, tags="selection_ui"
                    )

    def _finalize_move_render(self):
        """Taşıma bitince garantili tam render."""
        try:
            self._multi_drag = False
            for o in self.objects:
                o.pop("_drag_hide", None)
            self.canvas.delete("drag_preview")
            self.canvas.delete("text_size_preview")
            self.invalidate_cache()
            self.redraw(exclude_selected=False)
            self.draw_selection_ui()
        except Exception:
            pass

    def redraw(self, exclude_selected=False):
        """Ana çizim fonksiyonu"""
        if not self.original_image:
            return

        # Sürüklerken her zaman seçilileri bitmap'ten çıkar (çift yazı/şekil önler)
        dragging = bool(getattr(self, "_multi_drag", False))
        if dragging:
            exclude_selected = True

        # Sürükleme dışındayken hayalet önizlemeleri temizle
        if not exclude_selected and not dragging:
            for item in getattr(self, "drag_items", []) or []:
                try:
                    self.canvas.delete(item)
                except Exception:
                    pass
            self.drag_items = []
            self.canvas.delete("drag_preview")

        for item in getattr(self, "temp_items", []) or []:
            try:
                self.canvas.delete(item)
            except Exception:
                pass
        self.temp_items = []

        self.canvas.delete("bg_image")
        self.canvas.delete("snap_guide")
        self._guide_items = []
        # drag_preview'i silme: sürüklerken üstte kalır; draw_fast yeniler

        preview_img = self.render_preview(exclude_selected=exclude_selected)

        # Tk PhotoImage alpha'yı çoğu sistemde göstermez; önizlemede
        # canvas rengi üzerine composite ederek şeffaflığı görünür yap
        # tema canvas rengi
        try:
            hx = (self.colors.get("canvas") or "#0d1117").lstrip("#")
            canvas_bg = (int(hx[0:2], 16), int(hx[2:4], 16), int(hx[4:6], 16), 255)
        except Exception:
            canvas_bg = (0x0d, 0x11, 0x17, 255)
        display = Image.new("RGBA", preview_img.size, canvas_bg)
        display = Image.alpha_composite(display, preview_img.convert("RGBA"))

        # HQ cache — logical scale ile birebir
        self._hq_pil = display
        self._hq_scale = self.scale
        self._view_scale = self.scale

        self.rendered_objects_img = ImageTk.PhotoImage(display)

        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()

        if cw <= 1 or ch <= 1:
            self.root.after(50, lambda: self.redraw(exclude_selected))
            return

        self.img_x = max(0, (cw - display.width) // 2)
        self.img_y = max(0, (ch - display.height) // 2)

        draw_x = self.img_x + self.pan_x
        draw_y = self.img_y + self.pan_y
        self.canvas.create_image(
            draw_x, draw_y,
            anchor=tk.NW,
            image=self.rendered_objects_img,
            tags="bg_image"
        )
        self.canvas.tag_lower("bg_image")

        self.draw_selection_ui()
        if self.edge_crop:
            self.draw_edge_crop_ui()
        # Sürükleme sürerken önizlemeyi yeniden çiz (bg yenilendi)
        if dragging:
            self.draw_fast_drag_preview()

    def _preview_shape_label_on_canvas(self, obj, cx1, cy1, cx2, cy2, sc):
        """Sürükleme önizlemesi — hafif (PIL fit yok, kasma olmaz)."""
        text = obj.get("label")
        if not text:
            return
        box_w = abs(cx2 - cx1)
        box_h = abs(cy2 - cy1)
        if box_w < 10 or box_h < 10:
            return  # çok küçük: sadece çerçeve yeterli
        # kaba punto + yüksek zoom tavanı (kasma önler)
        fsize = max(7, min(int(obj.get("label_size", 18) * sc), int(box_h * 0.45), int(box_w / max(3, len(text) * 0.55)), 36))
        color = obj.get("label_color") or obj.get("color") or "#000000"
        # tek satır, ortala; uzunsa kısalt
        max_chars = max(1, int(box_w / max(4, fsize * 0.55)))
        shown = text if len(text) <= max_chars else text[: max(1, max_chars - 1)] + "…"
        self.drag_items.append(
            self.canvas.create_text(
                (cx1 + cx2) / 2.0, (cy1 + cy2) / 2.0,
                text=shown,
                fill=color,
                font=("Segoe UI", fsize),
                anchor="center",
                tags="drag_preview",
            )
        )

    def _preview_one_obj(self, obj, sc):
        """Tek nesne canvas önizlemesi; drag_items listesine ekler."""
        if not obj:
            return
        w = max(1, int(obj.get('width', 2) * sc))
        col = obj.get('color') or '#e94560'
        op = int(obj.get('opacity', 100) or 100)
        # Tk canvas fill şeffaflık desteklemez — solid görünmesin
        fill = obj.get('fill', "") or ""
        if op < 100:
            fill = ""  # sadece kenar; zoom/release'te gerçek şeffaf render gelir
        if obj['type'] == 'pen' and len(obj.get('points', [])) > 1:
            pts = [
                (self.img_x + self.pan_x + p[0] * sc,
                 self.img_y + self.pan_y + p[1] * sc)
                for p in obj['points']
            ]
            flat = [c for p in pts for c in p]
            self.drag_items.append(
                self.canvas.create_line(
                    flat, fill=col, width=w,
                    capstyle=tk.ROUND, smooth=True, tags="drag_preview"
                )
            )
            return
        if obj['type'] == 'curve' and obj.get('points'):
            pts = [
                (self.img_x + self.pan_x + p[0] * sc,
                 self.img_y + self.pan_y + p[1] * sc)
                for p in obj['points']
            ]
            flat = [c for p in pts for c in p]
            if len(flat) >= 4:
                self.drag_items.append(
                    self.canvas.create_line(
                        flat, fill=col, width=w, smooth=True, tags="drag_preview"
                    )
                )
            return
        cx1 = self.img_x + self.pan_x + (obj.get('x1', 0) * sc)
        cy1 = self.img_y + self.pan_y + (obj.get('y1', 0) * sc)
        if obj['type'] == 'circle':
            cx2 = self.img_x + self.pan_x + (obj.get('x2', 0) * sc)
            cy2 = self.img_y + self.pan_y + (obj.get('y2', 0) * sc)
            self.drag_items.append(
                self.canvas.create_oval(
                    cx1, cy1, cx2, cy2,
                    outline=col, fill=fill, width=w, tags="drag_preview"
                )
            )
            if obj.get('label'):
                self._preview_shape_label_on_canvas(obj, cx1, cy1, cx2, cy2, sc)
        elif obj['type'] in ('rect', 'square', 'triangle', 'hexagon', 'star', 'callout'):
            cx2 = self.img_x + self.pan_x + (obj.get('x2', 0) * sc)
            cy2 = self.img_y + self.pan_y + (obj.get('y2', 0) * sc)
            pts = self._shape_points(obj, cx1, cy1, cx2, cy2)
            flat = [c for p in pts for c in p]
            if len(flat) >= 6:
                self.drag_items.append(
                    self.canvas.create_polygon(
                        flat, outline=col, fill=fill, width=w, tags="drag_preview"
                    )
                )
            if obj.get('label'):
                self._preview_shape_label_on_canvas(obj, cx1, cy1, cx2, cy2, sc)
        elif obj['type'] == 'arrow':
            pts = obj.get('points')
            if pts and len(pts) >= 2:
                flat = []
                for p in pts:
                    flat.extend([
                        self.img_x + self.pan_x + p[0] * sc,
                        self.img_y + self.pan_y + p[1] * sc,
                    ])
                self.drag_items.append(
                    self.canvas.create_line(
                        *flat, fill=col, width=w, arrow=tk.LAST, tags="drag_preview"
                    )
                )
            else:
                cx2 = self.img_x + self.pan_x + (obj.get('x2', 0) * sc)
                cy2 = self.img_y + self.pan_y + (obj.get('y2', 0) * sc)
                self.drag_items.append(
                    self.canvas.create_line(
                        cx1, cy1, cx2, cy2,
                        fill=col, width=w, arrow=tk.LAST, tags="drag_preview"
                    )
                )
        elif obj['type'] in ('text', 'textbox'):
            # Orijinal font boyutu × görünüm ölçeği (büyütme yok)
            base_size = float(obj.get('size', 24) or 24)
            fs = max(6, int(round(base_size * sc)))
            # aşırı zoom'da Tk font tavanı (görünüm bozulmasın, size değişmez)
            fs = min(fs, 200)
            raw = str(obj.get('text', '') or '')
            bg = obj.get('bg_color') or ''
            tid = self.canvas.create_text(
                cx1, cy1, text=raw if raw else " ", fill=col,
                font=("Segoe UI", fs), anchor="nw", tags="drag_preview",
            )
            try:
                bb = self.canvas.bbox(tid)
            except Exception:
                bb = None
            if bg and bb:
                pad = max(2, int(fs * 0.1))
                self.drag_items.append(
                    self.canvas.create_rectangle(
                        bb[0] - pad, bb[1] - pad, bb[2] + pad, bb[3] + pad,
                        fill=bg, outline="", tags="drag_preview",
                    )
                )
                # metni üstte tut
                try:
                    self.canvas.tag_raise(tid)
                except Exception:
                    pass
            self.drag_items.append(tid)
        elif obj['type'] in ('image', 'fill_region'):
            cx2 = self.img_x + self.pan_x + (obj.get('x2', 0) * sc)
            cy2 = self.img_y + self.pan_y + (obj.get('y2', 0) * sc)
            # Canlı resim önizlemesi (makul boyutta)
            img = obj.get("pil_image")
            if obj['type'] == 'image' and img is not None:
                try:
                    tw = max(1, int(abs(cx2 - cx1)))
                    th = max(1, int(abs(cy2 - cy1)))
                    if tw * th <= 900 * 900:
                        thumb = img.copy()
                        if thumb.mode != "RGBA":
                            thumb = thumb.convert("RGBA")
                        thumb = thumb.resize((tw, th), Image.Resampling.BILINEAR)
                        from PIL import ImageTk
                        tkimg = ImageTk.PhotoImage(thumb)
                        if not hasattr(self, "_drag_photos"):
                            self._drag_photos = []
                        self._drag_photos.append(tkimg)
                        # son 8 kare tut
                        self._drag_photos = self._drag_photos[-8:]
                        self.drag_items.append(
                            self.canvas.create_image(
                                min(cx1, cx2), min(cy1, cy2),
                                image=tkimg, anchor="nw", tags="drag_preview",
                            )
                        )
                except Exception:
                    pass
            self.drag_items.append(
                self.canvas.create_rectangle(
                    cx1, cy1, cx2, cy2,
                    outline=self.colors["accent"], width=2, dash=(4, 2), tags="drag_preview",
                )
            )

    def draw_fast_drag_preview(self):
        """Sürükleme: anlık önizleme (hafif throttle)."""
        now = getattr(self, "_drag_preview_ts", 0)
        t = time.perf_counter()
        min_dt = 0.008  # ~120fps üst sınır — anlık his
        if t - now < min_dt and getattr(self, "_multi_drag", False):
            if getattr(self, "_drag_preview_after", None) is None:
                delay = max(1, int((min_dt - (t - now)) * 1000))
                self._drag_preview_after = self.root.after(delay, self._flush_drag_preview)
            return
        self._drag_preview_ts = t
        if getattr(self, "_drag_preview_after", None) is not None:
            try:
                self.root.after_cancel(self._drag_preview_after)
            except Exception:
                pass
            self._drag_preview_after = None
        self._draw_fast_drag_preview_now()

    def _flush_drag_preview(self):
        self._drag_preview_after = None
        self._drag_preview_ts = 0
        self._draw_fast_drag_preview_now()

    def _draw_fast_drag_preview_now(self):
        for item in self.drag_items:
            try:
                self.canvas.delete(item)
            except Exception:
                pass
        self.drag_items.clear()
        self.canvas.delete("drag_preview")
        self.canvas.delete("text_size_preview")
        self.canvas.delete("text_entry_vis")
        self.canvas.delete("text_entry_dash")
        self.canvas.delete("text_entry_caret")
        self.canvas.delete("text_entry_bg")

        objs = list(getattr(self, "selected_objs", None) or [])
        if not objs and self.selected_obj:
            objs = [self.selected_obj]
        if not objs:
            return

        sc = self._vs()
        for obj in objs:
            self._preview_one_obj(obj, sc)

        # Seçim çerçeveleri
        self.canvas.delete("selection_ui")
        self.handle_rects = []
        for obj in objs:
            if "x1" not in obj and obj.get("type") not in ("pen", "curve"):
                continue
            if obj.get("type") in ("pen", "curve") and obj.get("points"):
                xs = [self.img_x + self.pan_x + p[0] * sc for p in obj["points"]]
                ys = [self.img_y + self.pan_y + p[1] * sc for p in obj["points"]]
                if not xs:
                    continue
                self.canvas.create_rectangle(
                    min(xs), min(ys), max(xs), max(ys),
                    outline="#00e5ff", dash=(3, 2), width=1, tags="selection_ui"
                )
            else:
                cx1 = self.img_x + self.pan_x + obj.get("x1", 0) * sc
                cy1 = self.img_y + self.pan_y + obj.get("y1", 0) * sc
                cx2 = self.img_x + self.pan_x + obj.get("x2", obj.get("x1", 0)) * sc
                cy2 = self.img_y + self.pan_y + obj.get("y2", obj.get("y1", 0)) * sc
                self.canvas.create_rectangle(
                    min(cx1, cx2), min(cy1, cy2), max(cx1, cx2), max(cy1, cy2),
                    outline=self.colors["accent"] if obj == self.selected_obj else "#00e5ff",
                    dash=(2, 2), width=2 if obj == self.selected_obj else 1,
                    tags="selection_ui",
                )
        try:
            self.canvas.tag_raise("drag_preview")
            self.canvas.tag_raise("selection_ui")
            self.canvas.tag_raise("snap_guide")
        except Exception:
            pass

    def start_pan(self, event):
        # Ok yolu çizilirken sağ tık = bitir
        if getattr(self, "_arrow_path", None):
            self._finish_arrow_path()
            return
        # Metin kutusu açıksa kapat
        if getattr(self, "_text_entry", None):
            self.cancel_inline_text()
            return
        # Açık özellik penceresini kapat
        if getattr(self, "_ctx_win", None):
            try:
                self._ctx_win.destroy()
            except Exception:
                pass
            self._ctx_win = None

        # Sağ tık: yalnızca pan / seç aracına geç (özellik paneli yok)
        self.is_panning = True
        self._interaction_mode = True
        self.pan_start_x, self.pan_start_y = event.x, event.y
        self.set_action("move")
        self.canvas.config(cursor="fleur")
        self.status_label.config(
            text="✋ Kaydır",
            fg=self.colors["text"],
        )

    def do_pan(self, event):
        if not self.is_panning:
            return
        dx = event.x - self.pan_start_x
        dy = event.y - self.pan_start_y
        self.pan_x += dx
        self.pan_y += dy
        self.pan_start_x, self.pan_start_y = event.x, event.y
        self.canvas.move("bg_image", dx, dy)
        self.canvas.move("selection_ui", dx, dy)
        self.canvas.move("movable", dx, dy)
        self.canvas.move("drag_preview", dx, dy)

    def end_pan(self, event):
        if not self.is_panning:
            return
        self.is_panning = False
        self._interaction_mode = False
        cur = "fleur" if self.action == "move" else "cross"
        self.canvas.config(cursor=cur)
        self.draw_selection_ui()

    def _hit_object_at_canvas(self, cx, cy):
        """Canvas tıklamasında movable nesne bul (kilitliler hariç)."""
        try:
            items = self.canvas.find_overlapping(cx - 3, cy - 3, cx + 3, cy + 3)
        except Exception:
            items = ()
        for item in reversed(items):
            tags = self.canvas.gettags(item)
            if "movable" not in tags:
                continue
            for obj in self.objects:
                if obj.get("id") == item:
                    if self._is_locked(obj):
                        return None
                    return obj
        # koordinat yedek
        try:
            rx, ry = self.to_real_coords(cx, cy)
        except Exception:
            return None
        best, best_a = None, None
        for obj in reversed(self.objects):
            if self._is_locked(obj):
                continue
            try:
                x1, y1 = float(obj.get("x1", 0)), float(obj.get("y1", 0))
                x2, y2 = float(obj.get("x2", x1)), float(obj.get("y2", y1))
            except Exception:
                continue
            if obj.get("type") in ("pen", "curve", "arrow") and obj.get("points"):
                xs = [p[0] for p in obj["points"]]
                ys = [p[1] for p in obj["points"]]
                x1, x2, y1, y2 = min(xs), max(xs), min(ys), max(ys)
            if min(x1, x2) <= rx <= max(x1, x2) and min(y1, y2) <= ry <= max(y1, y2):
                area = abs(x2 - x1) * abs(y2 - y1)
                if best is None or area < best_a:
                    best, best_a = obj, area
        return best


    def show_object_context_menu(self, event, obj):
        """Sağ tık: kalınlık / font / şeffaflık ayarı."""
        if getattr(self, "_ctx_win", None):
            try:
                self._ctx_win.destroy()
            except Exception:
                pass
        win = tk.Toplevel(self.root)
        self._ctx_win = win
        win.title("Özellikler")
        win.configure(bg=self.colors["bg_medium"])
        win.transient(self.root)
        win.resizable(False, False)
        # imleç yanında
        try:
            win.geometry(f"+{event.x_root + 8}+{event.y_root + 8}")
        except Exception:
            pass
        win.attributes("-topmost", True)

        t = obj.get("type")
        has_label = bool(obj.get("label"))
        is_text = t in ("text", "textbox")
        is_stroke = t in ("pen", "curve", "arrow", "rect", "square", "circle",
                          "triangle", "hexagon", "star", "callout")

        tk.Label(
            win, text="⚙️ Özellikler",
            bg=self.colors["bg_medium"], fg=self.colors["accent"],
            font=("Segoe UI", 11, "bold"),
        ).pack(anchor="w", padx=12, pady=(10, 6))

        self._suspend_prop_trace = True

        def add_scale(label, from_, to_, value, on_change):
            fr = tk.Frame(win, bg=self.colors["bg_medium"])
            fr.pack(fill=tk.X, padx=12, pady=4)
            tk.Label(fr, text=label, bg=self.colors["bg_medium"], fg=self.colors["text"],
                     font=("Segoe UI", 9)).pack(anchor="w")
            var = tk.IntVar(value=int(value))
            sc = tk.Scale(
                fr, from_=from_, to=to_, orient=tk.HORIZONTAL, variable=var,
                bg=self.colors["bg_medium"], fg=self.colors["text"],
                highlightthickness=0, troughcolor=self.colors["bg_light"],
                length=200, command=lambda v: on_change(int(float(v))),
            )
            sc.pack(fill=tk.X)
            return var

        def apply_redraw():
            self.invalidate_cache()
            self.redraw()

        def add_color_btn(label, current, on_pick):
            fr = tk.Frame(win, bg=self.colors["bg_medium"])
            fr.pack(fill=tk.X, padx=12, pady=3)
            tk.Label(fr, text=label, bg=self.colors["bg_medium"], fg=self.colors["text"],
                     font=("Segoe UI", 9), width=14, anchor="w").pack(side=tk.LEFT)
            sw = tk.Button(fr, text="  ", width=3, relief="flat", cursor="hand2",
                           bg=current or "#888888")
            def _pick(btn=sw):
                c = colorchooser.askcolor(color=current or "#ffffff", title=label)[1]
                if c:
                    on_pick(c)
                    try:
                        btn.config(bg=c)
                    except Exception:
                        pass
                    apply_redraw()
            sw.config(command=_pick)
            sw.pack(side=tk.LEFT, padx=4)
            return sw

        # --- Renkler ---
        if is_text:
            add_color_btn("🔤 Font rengi", obj.get("color") or "#000000",
                          lambda c: (obj.__setitem__("color", c), setattr(self, "outline_color", c),
                                     self.btn_outline_color.config(bg=c)))
            add_color_btn("BG Arka plan", obj.get("bg_color") or "#ffffff",
                          lambda c: (obj.__setitem__("bg_color", c), setattr(self, "text_bg_color", c),
                                     setattr(self, "text_bg_color", c), apply_redraw()))
            fr_bg = tk.Frame(win, bg=self.colors["bg_medium"])
            fr_bg.pack(fill=tk.X, padx=12, pady=0)
            def clear_bg():
                obj["bg_color"] = ""
                self.text_bg_color = ""
                apply_redraw()
            tk.Button(fr_bg, text="✖ BG yok", command=clear_bg,
                      bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
                      font=("Segoe UI", 8), cursor="hand2").pack(anchor="w")
            add_scale("🔤 Font boyutu", 8, 150, obj.get("size", 24),
                      lambda v: (obj.__setitem__("size", v), self.font_size.set(v), apply_redraw()))
            add_scale("👻 Şeffaflık", 1, 100, obj.get("opacity", 100),
                      lambda v: (obj.__setitem__("opacity", v), self.opacity.set(v), apply_redraw()))
        elif is_stroke:
            add_color_btn("🖊 Kenar rengi", obj.get("color") or self.outline_color,
                          lambda c: (obj.__setitem__("color", c), setattr(self, "outline_color", c),
                                     self.btn_outline_color.config(bg=c)))
            if t not in ("pen", "arrow", "curve"):
                add_color_btn("🪣 Dolgu rengi", obj.get("fill") or "#cccccc",
                              lambda c: (obj.__setitem__("fill", c), setattr(self, "fill_color", c),
                                         self.btn_fill_color.config(bg=c, text="Renk")))
                # dolguyu temizle
                fr_clear = tk.Frame(win, bg=self.colors["bg_medium"])
                fr_clear.pack(fill=tk.X, padx=12, pady=0)
                def clear_fill():
                    obj["fill"] = ""
                    apply_redraw()
                tk.Button(fr_clear, text="✖ Dolgu yok", command=clear_fill,
                          bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
                          font=("Segoe UI", 8), cursor="hand2").pack(anchor="w")
            if has_label:
                add_color_btn("🔤 Font rengi", obj.get("label_color") or obj.get("color") or "#000000",
                              lambda c: obj.__setitem__("label_color", c))
                add_scale("🔤 Şekil metni font", 8, 150, obj.get("label_size", 18),
                          lambda v: (obj.__setitem__("label_size", v), self.font_size.set(v), apply_redraw()))
            add_scale("📏 Kalınlık", 1, 40, obj.get("width", 3),
                      lambda v: (obj.__setitem__("width", v), self.thickness.set(v), apply_redraw()))
            add_scale("👻 Şeffaflık", 1, 100, obj.get("opacity", 100),
                      lambda v: (obj.__setitem__("opacity", v), self.opacity.set(v), apply_redraw()))
        else:
            # image / fill_region
            if t == "fill_region":
                def _recolor_fill(c):
                    obj["color"] = c
                    im = obj.get("pil_image")
                    if im is not None:
                        try:
                            hx = c.lstrip("#")
                            fr, fg, fb = int(hx[0:2], 16), int(hx[2:4], 16), int(hx[4:6], 16)
                            px = im.load()
                            w, h = im.size
                            for yy in range(h):
                                for xx in range(w):
                                    p = px[xx, yy]
                                    if len(p) > 3 and p[3] > 0:
                                        px[xx, yy] = (fr, fg, fb, p[3])
                            obj.pop("_rz_cache", None)
                        except Exception:
                            pass
                add_color_btn("🪣 Dolgu rengi", obj.get("color") or "#3498db", _recolor_fill)
            add_scale("👻 Şeffaflık", 1, 100, obj.get("opacity", 100),
                      lambda v: (obj.__setitem__("opacity", v), self.opacity.set(v), apply_redraw()))

        def close_ctx():
            self._suspend_prop_trace = False
            try:
                win.destroy()
            except Exception:
                pass
            self._ctx_win = None

        # Kilit
        lock_fr = tk.Frame(win, bg=self.colors["bg_medium"])
        lock_fr.pack(fill=tk.X, padx=12, pady=6)
        locked_now = self._is_locked(obj)
        lock_var = tk.BooleanVar(value=locked_now)
        def on_lock():
            obj["locked"] = True if lock_var.get() else False
            self.save_state()
            if obj["locked"]:
                self.selected_objs = [o for o in self.selected_objs if o is not obj]
                if self.selected_obj is obj:
                    self.selected_obj = self.selected_objs[-1] if self.selected_objs else None
                try:
                    win.destroy()
                except Exception:
                    pass
                self._ctx_win = None
            apply_redraw()
            self.draw_selection_ui()
            self.status_label.config(
                text=("🔒 Kilitlendi — artık seçilemez" if obj["locked"] else "🔓 Kilit açıldı"),
                fg=self.colors["success"],
            )
        tk.Checkbutton(
            lock_fr, text="🔒 Kilitle (taşınamaz / silinemez)  ·  Ctrl+L",
            variable=lock_var, command=on_lock,
            bg=self.colors["bg_medium"], fg=self.colors["text"],
            selectcolor=self.colors["bg_light"], activebackground=self.colors["bg_medium"],
            font=("Segoe UI", 9), anchor="w",
        ).pack(fill=tk.X)

        row = tk.Frame(win, bg=self.colors["bg_medium"])
        row.pack(fill=tk.X, padx=12, pady=4)
        def do_copy():
            self.copy_style()
        def do_paste():
            self.paste_style()
            apply_redraw()
        tk.Button(row, text="📋 Stil Kopyala", command=do_copy,
                  bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
                  font=("Segoe UI", 8), cursor="hand2").pack(side=tk.LEFT, padx=2)
        tk.Button(row, text="📥 Stil Yapıştır", command=do_paste,
                  bg=self.colors["bg_light"], fg=self.colors["text"], relief="flat",
                  font=("Segoe UI", 8), cursor="hand2").pack(side=tk.LEFT, padx=2)

        tk.Button(
            win, text="Tamam", command=close_ctx,
            bg=self.colors["accent"], fg="white", relief="flat",
            font=("Segoe UI", 9, "bold"), padx=12, pady=4, cursor="hand2",
        ).pack(pady=(8, 12))
        win.protocol("WM_DELETE_WINDOW", close_ctx)
        win.bind("<Escape>", lambda e: close_ctx())


    def start_page_edge_crop(self):
        """Sayfa kenar tutamaçlı kırpma modu."""
        if not self.original_image:
            return
        w, h = self.original_image.size
        self.edge_crop = {
            "mode": "page",
            "l": 0.0, "t": 0.0, "r": float(w), "b": float(h),
            "obj": None,
        }
        self.edge_crop_handle = None
        if self.action == "crop":
            self.action = "move"
        self.draw_edge_crop_ui()
        self.status_label.config(
            text="✂ Mavi tutamaçları sürükle | Enter: uygula | Esc: iptal",
            fg=self.colors["warning"]
        )

    def start_page_resize(self):
        """Sayfayı kenarlardan uzat/kısalt (butonla açılır)."""
        if not self.original_image:
            return
        w, h = self.original_image.size
        self.edge_crop = {
            "mode": "page_resize",
            "l": 0.0, "t": 0.0, "r": float(w), "b": float(h),
            "obj": None,
        }
        self.edge_crop_handle = None
        if self.action == "crop":
            self.action = "move"
        self.draw_edge_crop_ui()
        self.status_label.config(
            text="↔ Kenarlardan uzat/kısalt | Enter: uygula | Esc: iptal",
            fg=self.colors["warning"],
        )

    def start_image_edge_crop(self, obj):
        """Eklenen resim için kenar tutamaçlı kırpma/boyutlandırma."""
        if not obj or obj.get("type") != "image":
            return
        self.selected_obj = obj
        self.edge_crop = {
            "mode": "image",
            "l": float(obj.get("x1", 0)),
            "t": float(obj.get("y1", 0)),
            "r": float(obj.get("x2", 0)),
            "b": float(obj.get("y2", 0)),
            "obj": obj,
            "orig_box": (
                float(obj.get("x1", 0)), float(obj.get("y1", 0)),
                float(obj.get("x2", 0)), float(obj.get("y2", 0)),
            ),
        }
        self.edge_crop_handle = None
        if self.action == "crop":
            self.action = "move"
        self.draw_edge_crop_ui()

    def cancel_edge_crop(self, silent=False, event=None):
        if not self.edge_crop:
            return
        self.edge_crop = None
        self.edge_crop_handle = None
        self.canvas.delete("edge_crop")
        if self.action in ("crop", "crop_region"):
            self.action = "move"
        if not silent:
            self.status_label.config(text="Kırpma iptal", fg=self.colors["warning"])
        self.draw_selection_ui()

    def apply_edge_crop(self, event=None):
        if not self.edge_crop:
            return
        ec = self.edge_crop
        l, t, r, b = ec["l"], ec["t"], ec["r"], ec["b"]
        if r - l < 2 or b - t < 2:
            self.status_label.config(text="Kırpma alanı çok küçük", fg=self.colors["warning"])
            return

        if ec["mode"] == "page_resize":
            self.save_state()
            old = self.original_image
            ow, oh = old.size
            # l,t,r,b sayfa koordinatı (negatif olabilir)
            nl, nt, nr, nb = float(l), float(t), float(r), float(b)
            if nr < nl:
                nl, nr = nr, nl
            if nb < nt:
                nt, nb = nb, nt
            new_w = max(50, int(round(nr - nl)))
            new_h = max(50, int(round(nb - nt)))
            new_w = min(20000, new_w)
            new_h = min(20000, new_h)
            new_img = Image.new("RGBA", (new_w, new_h), (255, 255, 255, 255))
            paste_x = int(round(-nl))
            paste_y = int(round(-nt))
            try:
                if old.mode != "RGBA":
                    old = old.convert("RGBA")
                new_img.paste(old, (paste_x, paste_y), old)
            except Exception:
                new_img.paste(old.convert("RGBA"), (paste_x, paste_y))
            self.original_image = new_img
            # nesneleri kaydır
            dx, dy = -nl, -nt
            for obj in self.objects:
                if obj.get("points"):
                    obj["points"] = [(p[0] + dx, p[1] + dy) for p in obj["points"]]
                obj["x1"] = obj.get("x1", 0) + dx
                obj["y1"] = obj.get("y1", 0) + dy
                if "x2" in obj:
                    obj["x2"] = obj.get("x2", 0) + dx
                    obj["y2"] = obj.get("y2", 0) + dy
            self.invalidate_cache()
            self.pan_x = self.pan_y = 0
            cw = self.canvas.winfo_width()
            ch = self.canvas.winfo_height()
            if cw > 1 and ch > 1:
                self.scale = min(
                    (cw - 40) / max(1, new_w),
                    (ch - 40) / max(1, new_h),
                    1.0,
                )
            self._initial_scale = self.scale
            self.edge_crop = None
            self.edge_crop_handle = None
            self.action = "move"
            self.canvas.delete("edge_crop")
            self.redraw()
            self.status_label.config(
                text=f"↔ Sayfa boyutu: {new_w}×{new_h}",
                fg=self.colors["success"],
            )
            return

        if ec["mode"] == "page":
            pw, ph = self.original_image.size
            left_i = max(0, min(pw - 1, int(l)))
            top_i = max(0, min(ph - 1, int(t)))
            right_i = max(left_i + 1, min(pw, int(r)))
            bottom_i = max(top_i + 1, min(ph, int(b)))
            self.save_state()
            self.original_image = self.original_image.crop((left_i, top_i, right_i, bottom_i))
            self.invalidate_cache()
            for obj in self.objects:
                if "points" in obj:
                    obj["points"] = [(p[0] - left_i, p[1] - top_i) for p in obj["points"]]
                else:
                    obj["x1"] = obj.get("x1", 0) - left_i
                    obj["y1"] = obj.get("y1", 0) - top_i
                    if obj.get("type") in ("rect", "square", "circle", "triangle", "hexagon", "star", "callout", "arrow", "image", "curve"):
                        obj["x2"] = obj.get("x2", 0) - left_i
                        obj["y2"] = obj.get("y2", 0) - top_i
            self.pan_x = 0
            self.pan_y = 0
            cw = self.canvas.winfo_width()
            ch = self.canvas.winfo_height()
            if cw > 1 and ch > 1:
                self.scale = min(
                    (cw - 40) / max(1, self.original_image.width),
                    (ch - 40) / max(1, self.original_image.height),
                )
            self._initial_scale = self.scale
            self.edge_crop = None
            self.edge_crop_handle = None
            self.action = "move"
            self.canvas.delete("edge_crop")
            self.redraw()
            self.status_label.config(
                text=f"✂ Sayfa kırpıldı — {self.original_image.width}×{self.original_image.height}",
                fg=self.colors["success"],
            )

        elif ec["mode"] == "image" and ec.get("obj"):
            obj = ec["obj"]
            if obj not in self.objects:
                self.cancel_edge_crop(silent=True)
                return
            self.save_state()
            ol, ot, orr, ob = ec.get("orig_box", (obj["x1"], obj["y1"], obj["x2"], obj["y2"]))
            ow, oh = max(1e-6, orr - ol), max(1e-6, ob - ot)
            # Yeni kutu sayfa koordinatında
            nl, nt, nr, nb = l, t, r, b
            # İçerik kırpma: orijinal kutuya göre göreli oran
            # Sürükleme hem boyut hem konum değiştirdi; pil'i görünen orana göre crop
            src = obj.get("pil_image")
            if src is not None:
                sw, sh = src.size
                # Mevcut kutu ile orijinal kutu kesişimi oranları
                # Basit yaklaşım: sadece bbox güncelle (yeniden boyutlandırma)
                # Kenar içe çekildiyse içeriği de kırp
                rel_l = (nl - ol) / ow
                rel_t = (nt - ot) / oh
                rel_r = (nr - ol) / ow
                rel_b = (nb - ot) / oh
                # Clamp 0-1
                rel_l = max(0.0, min(1.0, rel_l))
                rel_t = max(0.0, min(1.0, rel_t))
                rel_r = max(0.0, min(1.0, rel_r))
                rel_b = max(0.0, min(1.0, rel_b))
                if rel_r - rel_l > 0.01 and rel_b - rel_t > 0.01:
                    cl = int(rel_l * sw)
                    ct = int(rel_t * sh)
                    cr = max(cl + 1, int(rel_r * sw))
                    cb = max(ct + 1, int(rel_b * sh))
                    try:
                        obj["pil_image"] = src.crop((cl, ct, cr, cb))
                        obj.pop("_rz_cache", None)
                    except Exception:
                        pass
            obj["x1"], obj["y1"], obj["x2"], obj["y2"] = nl, nt, nr, nb
            self.edge_crop = None
            self.edge_crop_handle = None
            self.action = "move"
            self.canvas.delete("edge_crop")
            self.redraw()
            self.status_label.config(text="✂ Resim kenarlardan güncellendi", fg=self.colors["success"])

    def draw_edge_crop_ui(self):
        self.canvas.delete("edge_crop")
        if not self.edge_crop:
            return
        ec = self.edge_crop
        sc = self._vs()
        l = self.img_x + self.pan_x + ec["l"] * sc
        t = self.img_y + self.pan_y + ec["t"] * sc
        r = self.img_x + self.pan_x + ec["r"] * sc
        b = self.img_y + self.pan_y + ec["b"] * sc
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()

        # Dışarıyı karart
        dim = "#000000"
        for coords in (
            (0, 0, cw, max(0, t)),
            (0, min(ch, b), cw, ch),
            (0, max(0, t), max(0, l), min(ch, b)),
            (min(cw, r), max(0, t), cw, min(ch, b)),
        ):
            self.canvas.create_rectangle(*coords, fill=dim, stipple="gray50", outline="", tags="edge_crop")

        self.canvas.create_rectangle(l, t, r, b, outline="#00e5ff", width=2, tags="edge_crop")
        hs = 7
        handles = {
            "nw": (l, t), "n": ((l + r) / 2, t), "ne": (r, t),
            "w": (l, (t + b) / 2), "e": (r, (t + b) / 2),
            "sw": (l, b), "s": ((l + r) / 2, b), "se": (r, b),
        }
        self._edge_handle_ids = {}
        for name, (hx, hy) in handles.items():
            hid = self.canvas.create_rectangle(
                hx - hs, hy - hs, hx + hs, hy + hs,
                fill="#00e5ff", outline="white", width=1, tags=("edge_crop", f"edge_h_{name}"),
            )
            self._edge_handle_ids[name] = hid

    def _hit_edge_handle(self, x, y):
        if not self.edge_crop:
            return None
        sc = self._vs()
        ec = self.edge_crop
        l = self.img_x + self.pan_x + ec["l"] * sc
        t = self.img_y + self.pan_y + ec["t"] * sc
        r = self.img_x + self.pan_x + ec["r"] * sc
        b = self.img_y + self.pan_y + ec["b"] * sc
        hs = 10
        pts = {
            "nw": (l, t), "n": ((l + r) / 2, t), "ne": (r, t),
            "w": (l, (t + b) / 2), "e": (r, (t + b) / 2),
            "sw": (l, b), "s": ((l + r) / 2, b), "se": (r, b),
        }
        for name, (hx, hy) in pts.items():
            if abs(x - hx) <= hs and abs(y - hy) <= hs:
                return name
        return None



    def start_inline_text(self, canvas_x, canvas_y, real_x, real_y, initial="", edit_obj=None, anchor="nw", as_label=False, as_box=False):
        """Yerinde metin: gizli Entry (tüm harfler) + canvas önizleme."""
        self.cancel_inline_text()
        self._text_as_label = as_label
        self._text_as_box = False
        fs_page = self.font_size.get() if not edit_obj else edit_obj.get("size", self.font_size.get())
        color = (edit_obj.get("color") if edit_obj else None) or self.outline_color
        bg = (edit_obj.get("bg_color") if edit_obj else None) or (self.text_bg_color or "")
        sc = max(self._vs(), 0.35)
        fs = max(9, min(72, int(round(fs_page * sc))))
        self._text_buffer = initial or ""
        self._text_caret = len(self._text_buffer)
        self._text_entry_pos = (real_x, real_y)
        self._text_edit_obj = edit_obj
        self._text_entry_origin = (canvas_x, canvas_y)
        self._text_entry_fs = fs
        self._text_entry_color = color
        self._text_entry_bg = bg
        self._text_entry = "canvas"

        if edit_obj is not None and edit_obj.get("type") in ("text", "textbox"):
            edit_obj["_edit_hide"] = True
            edit_obj["_drag_hide"] = True
            self.invalidate_cache()
            self.redraw()

        # Gizli Entry — tüm klavye karakterlerini güvenle alır
        entry = tk.Entry(
            self.canvas,
            font=("Segoe UI", max(8, fs // 2)),
            fg=color,
            bg=self.colors.get("bg_dark", "#111111"),
            insertbackground=color,
            relief="flat",
            bd=0,
            highlightthickness=0,
        )
        if initial:
            entry.insert(0, initial)
            entry.icursor(tk.END)
        win = self.canvas.create_window(
            canvas_x, canvas_y, window=entry, anchor="nw",
            width=1, height=1, tags="text_entry",
        )
        self._text_entry_widget = entry
        self._text_entry_win = win
        self._caret_blink_on = True
        self._caret_after = None

        def stop_blink():
            aid = getattr(self, "_caret_after", None)
            if aid:
                try:
                    self.root.after_cancel(aid)
                except Exception:
                    pass
            self._caret_after = None

        def blink():
            if not getattr(self, "_text_entry", None):
                return
            self._caret_blink_on = not getattr(self, "_caret_blink_on", True)
            redraw_canvas_text()
            self._caret_after = self.root.after(530, blink)

        def sync_from_entry():
            try:
                if entry.winfo_exists():
                    self._text_buffer = entry.get()
                    self._text_caret = int(entry.index(tk.INSERT))
            except Exception:
                pass

        def redraw_canvas_text(_e=None):
            if not getattr(self, "_text_entry", None):
                return
            sync_from_entry()
            buf = self._text_buffer if self._text_buffer is not None else ""
            caret = max(0, min(len(buf), int(getattr(self, "_text_caret", 0))))
            self.canvas.delete("text_entry_vis")
            self.canvas.delete("text_entry_dash")
            self.canvas.delete("text_entry_bg")
            self.canvas.delete("text_entry_caret")
            ox, oy = self._text_entry_origin
            pad = 4 if bg else 2
            display = buf if buf else " "
            anch = "center" if getattr(self, "_text_as_label", False) else "nw"
            tid = self.canvas.create_text(
                ox if anch == "center" else ox + pad,
                oy if anch == "center" else oy + pad,
                text=display, fill=color, font=("Segoe UI", fs),
                anchor=anch, tags=("text_entry", "text_entry_vis"),
            )
            try:
                bbox = self.canvas.bbox(tid)
            except Exception:
                bbox = (ox, oy, ox + fs * 3, oy + fs + 4)
            if not buf:
                x1, y1 = ox, oy
                x2, y2 = ox + max(fs * 3, 36), oy + fs + 8
            else:
                x1, y1, x2, y2 = bbox
                x1 -= pad; y1 -= pad; x2 += pad; y2 += pad
            if bg:
                self.canvas.create_rectangle(
                    x1, y1, x2, y2, fill=bg, outline="",
                    tags=("text_entry", "text_entry_bg"),
                )
                try:
                    self.canvas.tag_lower("text_entry_bg", "text_entry_vis")
                except Exception:
                    pass
            self.canvas.create_rectangle(
                x1, y1, x2, y2,
                outline=self.colors.get("accent", "#e94560"),
                dash=(4, 3), width=1,
                tags=("text_entry", "text_entry_dash"),
            )
            # caret
            if getattr(self, "_caret_blink_on", True):
                pre = buf[:caret]
                if "\n" in pre:
                    line = pre.split("\n")[-1]
                    line_idx = pre.count("\n")
                else:
                    line = pre
                    line_idx = 0
                self.canvas.delete("_tmp_caret_m")
                mid = self.canvas.create_text(
                    (ox if anch == "center" else ox + pad),
                    (oy if anch == "center" else oy + pad) + line_idx * int(fs * 1.25),
                    text=line if line else "",
                    fill=color, font=("Segoe UI", fs),
                    anchor="nw", tags="_tmp_caret_m",
                )
                try:
                    bb = self.canvas.bbox(mid)
                    if bb:
                        cx = bb[2] if line else bb[0]
                        cy1, cy2 = bb[1], bb[3]
                    else:
                        cx = ox + pad
                        cy1, cy2 = oy + pad, oy + pad + fs
                except Exception:
                    cx = ox + pad
                    cy1, cy2 = oy + pad, oy + pad + fs
                self.canvas.delete("_tmp_caret_m")
                self.canvas.create_line(
                    cx + 1, cy1, cx + 1, cy2,
                    fill=color, width=2,
                    tags=("text_entry", "text_entry_caret"),
                )

        def on_key(event):
            if not getattr(self, "_text_entry", None):
                return
            key = event.keysym
            state = event.state
            ctrl = bool(state & 0x4)
            if key in ("Return", "KP_Enter"):
                if ctrl:
                    # Entry tek satır — newline enjekte
                    try:
                        i = entry.index(tk.INSERT)
                        entry.insert(i, "\n")
                    except Exception:
                        pass
                    self.root.after(1, redraw_canvas_text)
                    return "break"
                self.commit_inline_text()
                return "break"
            if key == "Escape":
                self.cancel_inline_text()
                return "break"
            # diğer tuşlar Entry'ye bırak; KeyRelease ile önizleme
            self.root.after(1, redraw_canvas_text)
            return None

        entry.bind("<Key>", on_key)
        entry.bind("<KeyRelease>", lambda e: redraw_canvas_text())
        entry.bind("<Control-Return>", lambda e: on_key(e))
        entry.bind("<Escape>", lambda e: self.cancel_inline_text())
        entry.focus_force()
        self.root.after(10, entry.focus_force)
        redraw_canvas_text()
        stop_blink()
        self._caret_blink_on = True
        self._caret_after = self.root.after(530, blink)
        self.status_label.config(
            text="🔤 Yaz · Enter=onay · Ctrl+Enter=satır · Esc=iptal",
            fg=self.colors["warning"],
        )

    def _focusout_commit_text(self):
        # canvas-key düzenlemede focusout ile otomatik commit yok
        return

    def commit_inline_text(self):
        entry = getattr(self, "_text_entry", None)
        if not entry:
            return
        text = ""
        w = getattr(self, "_text_entry_widget", None)
        try:
            if w is not None and w.winfo_exists():
                text = w.get()
            else:
                text = getattr(self, "_text_buffer", "") or ""
        except Exception:
            text = getattr(self, "_text_buffer", "") or ""
        text = text.rstrip()
        as_box = False
        pos = getattr(self, "_text_entry_pos", (0, 0))
        edit_obj = getattr(self, "_text_edit_obj", None)
        as_label = getattr(self, "_text_as_label", False)
        bg_save = getattr(self, "_text_entry_bg", "")
        self.cancel_inline_text()
        if edit_obj and edit_obj in self.objects and as_label:
            # Şekle bağlı etiket (şekille birlikte hareket eder)
            self.save_state()
            if text:
                edit_obj["label"] = text
                edit_obj["label_size"] = self.font_size.get()
                edit_obj["label_color"] = self.outline_color
            else:
                edit_obj.pop("label", None)
            self.invalidate_cache()
            self.redraw()
            self.status_label.config(
                text=(f"🔤 Şekil metni: {text[:40]}" if text else "Şekil metni silindi"),
                fg=self.colors["success"],
            )
            return
        if not text:
            self.status_label.config(text="Metin boş — eklenmedi", fg=self.colors["warning"])
            return
        self.save_state()
        if edit_obj and edit_obj in self.objects and edit_obj.get("type") in ("text", "textbox"):
            edit_obj["text"] = text
            if getattr(self, "_text_entry_bg", None) is not None:
                edit_obj["bg_color"] = self._text_entry_bg
            self.redraw()
            self.status_label.config(text=f"🔤 Metin güncellendi: {text[:40].replace(chr(10), ' ')}", fg=self.colors["success"])
            return
        obj_type = "textbox" if as_box else "text"
        bg = getattr(self, "_text_entry_bg", "") or (self.text_bg_color if as_box else self.text_bg_color)
        self.objects.append({
            "type": obj_type,
            "layer": self.current_layer_id,
            "x1": pos[0],
            "y1": pos[1],
            "color": self.outline_color,
            "text": text,
            "size": self.font_size.get(),
            "opacity": self.opacity.get(),
            "bg_color": bg or "",
            "rotation": 0,
        })
        self.redraw()
        self.status_label.config(
            text=f"{'📝' if as_box else '🔤'} Eklendi: {text[:40].replace(chr(10), ' ')}",
            fg=self.colors["success"],
        )

    def cancel_inline_text(self):
        # blink durdur
        aid = getattr(self, "_caret_after", None)
        if aid:
            try:
                self.root.after_cancel(aid)
            except Exception:
                pass
        self._caret_after = None
        # key unbind
        h = getattr(self, "_text_key_handler", None)
        if h:
            try:
                self.canvas.unbind("<Key>", h)
            except Exception:
                pass
            try:
                self.root.unbind("<Key>", h)
            except Exception:
                pass
            # add=+ ile unbind zor; handler kendini kapatır
            self._text_key_handler = None
        edit = getattr(self, "_text_edit_obj", None)
        if edit is not None:
            edit.pop("_edit_hide", None)
            edit.pop("_drag_hide", None)
        w = getattr(self, "_text_entry_widget", None)
        win = getattr(self, "_text_entry_win", None)
        if w is not None:
            try:
                w.destroy()
            except Exception:
                pass
        if win is not None:
            try:
                self.canvas.delete(win)
            except Exception:
                pass
        self.canvas.delete("text_entry")
        self.canvas.delete("text_entry_dash")
        self.canvas.delete("text_entry_vis")
        self.canvas.delete("text_entry_caret")
        self.canvas.delete("text_entry_bg")
        self._text_entry = None
        self._text_entry_widget = None
        self._text_entry_win = None
        self._text_entry_pos = None
        self._text_edit_obj = None
        self._text_as_label = False
        self._text_as_box = False
        self._text_buffer = ""
        if edit is not None:
            try:
                self.invalidate_cache()
                self.redraw()
            except Exception:
                pass


    def edit_text_object(self, obj):
        """Mevcut metin / metin kutusunu düzenle."""
        if not obj or obj.get("type") not in ("text", "textbox"):
            return
        if self._is_locked(obj):
            self.status_label.config(text="🔒 Kilitli metin düzenlenemez", fg=self.colors["warning"])
            return
        sc = self._vs()
        cx = self.img_x + self.pan_x + float(obj.get("x1", 0)) * sc
        cy = self.img_y + self.pan_y + float(obj.get("y1", 0)) * sc
        self._set_selection([obj], expand_groups=False)
        if obj.get("bg_color"):
            self.text_bg_color = obj.get("bg_color")
            pass
        self.start_inline_text(
            cx, cy, obj.get("x1", 0), obj.get("y1", 0),
            initial=str(obj.get("text", "")),
            edit_obj=obj,
            anchor="nw",
            as_box=(obj.get("type") == "textbox"),
        )

    def on_double_click(self, event):
        """Şekle çift tık → ortasına metin; ok yolunu bitir."""
        if self.action == "arrow_path" and getattr(self, "_arrow_path", None):
            try:
                rx, ry = self.to_real_coords(event.x, event.y)
            except Exception:
                self._finish_arrow_path()
                return
            rx, ry = self._snap_to_anchor(rx, ry)
            if self._arrow_path:
                lx, ly = self._arrow_path[-1]
                _, _, rx, ry = self._constrain_ortho_real(lx, ly, rx, ry)
                if abs(rx - lx) > 0.5 or abs(ry - ly) > 0.5:
                    self._arrow_path.append((rx, ry))
            self._finish_arrow_path()
            return
        if not self.original_image:
            return
        if self.edge_crop:
            return
        # Tıklanan nesneyi bul (geniş tolerans)
        hit = None
        try:
            items = self.canvas.find_overlapping(event.x - 8, event.y - 8, event.x + 8, event.y + 8)
        except Exception:
            items = ()
        for item in reversed(items):
            tags = self.canvas.gettags(item)
            if "movable" not in tags and "locked_nohit" not in tags:
                continue
            for obj in self.objects:
                if obj.get("id") == item:
                    hit = obj
                    break
            if hit:
                break
        if not hit:
            try:
                hit = self._hit_object_at_canvas(event.x, event.y)
            except Exception:
                hit = None
        if not hit:
            try:
                rx0, ry0 = self.to_real_coords(event.x, event.y)
            except Exception:
                return
            best, best_a = None, 1e18
            for obj in reversed(self.objects):
                if self._is_locked(obj):
                    continue
                t = obj.get("type")
                if t in ("text", "textbox"):
                    # metin ayrı
                    x1, y1 = float(obj.get("x1", 0)), float(obj.get("y1", 0))
                    fs = float(obj.get("size", 24) or 24)
                    if abs(rx0 - x1) < fs * 4 and abs(ry0 - y1) < fs * 2:
                        hit = obj
                        break
                    continue
                if t in ("pen", "curve", "arrow") and obj.get("points"):
                    xs = [p[0] for p in obj["points"]]
                    ys = [p[1] for p in obj["points"]]
                    x1, x2, y1, y2 = min(xs), max(xs), min(ys), max(ys)
                else:
                    x1, y1 = float(obj.get("x1", 0)), float(obj.get("y1", 0))
                    x2, y2 = float(obj.get("x2", x1)), float(obj.get("y2", y1))
                pad = 4.0
                if min(x1, x2) - pad <= rx0 <= max(x1, x2) + pad and min(y1, y2) - pad <= ry0 <= max(y1, y2) + pad:
                    area = max(1.0, abs(x2 - x1) * abs(y2 - y1))
                    if area < best_a:
                        best, best_a = obj, area
            if not hit:
                hit = best
        if not hit:
            self.status_label.config(text="Çift tık: şekil bulunamadı", fg=self.colors["warning"])
            return
        if self._is_locked(hit):
            self.status_label.config(text="🔒 Kilitli — metin eklenemez", fg=self.colors["warning"])
            return
        if hit.get("type") in ("text", "textbox"):
            self.edit_text_object(hit)
            return

        # Şekil ortası
        sc = self._vs()
        if hit.get("type") in ("pen", "curve", "arrow") and hit.get("points"):
            xs = [p[0] for p in hit["points"]]
            ys = [p[1] for p in hit["points"]]
            rx = (min(xs) + max(xs)) / 2
            ry = (min(ys) + max(ys)) / 2
        else:
            x1, y1 = float(hit.get("x1", 0)), float(hit.get("y1", 0))
            x2, y2 = float(hit.get("x2", x1)), float(hit.get("y2", y1))
            rx = (x1 + x2) / 2
            ry = (y1 + y2) / 2

        cx = self.img_x + self.pan_x + rx * sc
        cy = self.img_y + self.pan_y + ry * sc
        initial = str(hit.get("label", "") or "")
        self._set_selection([hit], expand_groups=False)
        self.start_inline_text(
            cx, cy, rx, ry,
            initial=initial,
            edit_obj=hit,
            anchor="center",
            as_label=True,
        )
        self.status_label.config(
            text="🔤 Şekil ortasına metin — Enter onay · Ctrl+Enter satır · Esc iptal",
            fg=self.colors["warning"],
        )


    def _sample_color_at(self, rx, ry):
        """Sayfa koordinatında görünen rengi al (RGBA hex)."""
        if not self.original_image:
            return None
        x, y = int(round(rx)), int(round(ry))
        w, h = self.original_image.size
        if not (0 <= x < w and 0 <= y < h):
            return None
        # Önce taban resim; üzerine nesne yoksa bu yeterli
        try:
            flat = self.render_for_export() if hasattr(self, "render_for_export") else self.original_image
        except Exception:
            flat = self.original_image
        if flat.mode != "RGBA":
            flat = flat.convert("RGBA")
        # export full size
        if flat.size != (w, h):
            flat = flat.resize((w, h), Image.Resampling.NEAREST)
        r, g, b, a = flat.getpixel((x, y))
        return f"#{r:02x}{g:02x}{b:02x}"

    def apply_eyedropper(self, rx, ry):
        hex_c = self._sample_color_at(rx, ry)
        if not hex_c:
            self.status_label.config(text="Renk alınamadı", fg=self.colors["warning"])
            return
        self.outline_color = hex_c
        self._default_outline = hex_c
        self.btn_outline_color.config(bg=hex_c)
        # dolgu da aynı (Paint davranışı)
        self.fill_color = hex_c
        try:
            self.btn_fill_color.config(bg=hex_c, text="Renk")
        except Exception:
            pass
        self.status_label.config(text=f"💧 Renk alındı: {hex_c}", fg=self.colors["success"])

    def _build_line_boundary_mask(self, w, h):
        """Çizgi/kontur pikselleri = 1, boş = 0. Sadece çizgiler sınır oluşturur."""
        mask = Image.new("1", (w, h), 0)
        draw = ImageDraw.Draw(mask)
        visible = {L["id"] for L in self.layers if L.get("visible")}

        def stroke_w(obj):
            return max(1, int(obj.get("width", 2)))

        for obj in self.objects:
            if obj.get("layer", 0) not in visible:
                continue
            t = obj.get("type")
            col = 1
            if t == "pen" and len(obj.get("points", [])) > 1:
                pts = [(int(p[0]), int(p[1])) for p in obj["points"]]
                draw.line(pts, fill=col, width=stroke_w(obj), joint="curve")
            elif t == "curve" and len(obj.get("points", [])) >= 2:
                pts = obj["points"]
                if len(pts) == 2:
                    draw.line([(int(pts[0][0]), int(pts[0][1])), (int(pts[1][0]), int(pts[1][1]))],
                              fill=col, width=stroke_w(obj))
                else:
                    p0, p1, p2 = pts[0], pts[1], pts[2]
                    samples = []
                    for i in range(48):
                        tt = i / 47.0
                        ax = (1 - tt) ** 2 * p0[0] + 2 * (1 - tt) * tt * p1[0] + tt ** 2 * p2[0]
                        ay = (1 - tt) ** 2 * p0[1] + 2 * (1 - tt) * tt * p1[1] + tt ** 2 * p2[1]
                        samples.append((int(ax), int(ay)))
                    draw.line(samples, fill=col, width=stroke_w(obj), joint="curve")
            elif t == "arrow":
                x1, y1 = int(obj.get("x1", 0)), int(obj.get("y1", 0))
                x2, y2 = int(obj.get("x2", 0)), int(obj.get("y2", 0))
                draw.line([(x1, y1), (x2, y2)], fill=col, width=stroke_w(obj))
            elif t in ("rect", "square", "circle", "triangle", "hexagon", "star", "callout"):
                # Sadece kontur (dolgu değil) — kapalı çizgi sınırı
                pts = self._shape_points(
                    obj, obj.get("x1", 0), obj.get("y1", 0),
                    obj.get("x2", 0), obj.get("y2", 0),
                )
                if len(pts) >= 2:
                    ip = [(int(p[0]), int(p[1])) for p in pts]
                    if t == "circle" and not obj.get("rotation") and not obj.get("flip_h") and not obj.get("flip_v"):
                        draw.ellipse(
                            [int(min(obj["x1"], obj["x2"])), int(min(obj["y1"], obj["y2"])),
                             int(max(obj["x1"], obj["x2"])), int(max(obj["y1"], obj["y2"]))],
                            outline=col, width=stroke_w(obj),
                        )
                    else:
                        draw.polygon(ip, outline=col)
                        # kalınlık için bir kez daha çizgi
                        if len(ip) >= 2:
                            draw.line(ip + [ip[0]], fill=col, width=stroke_w(obj))
        return mask

    def apply_bucket_fill(self, rx, ry):
        """Sadece çizgilerle kapalı bölgeyi doldur. Açık alan doldurulmaz."""
        if not self.original_image:
            return
        x, y = int(round(rx)), int(round(ry))
        img = self.original_image
        if img.mode != "RGBA":
            img = img.convert("RGBA")
            self.original_image = img
        w, h = img.size
        if not (0 <= x < w and 0 <= y < h):
            self.status_label.config(text="Sayfa dışında", fg=self.colors["warning"])
            return

        boundary = self._build_line_boundary_mask(w, h)
        bp = boundary.load()
        if bp[x, y] != 0:
            self.status_label.config(text="Çizginin üstüne tıklandı — boş alana tıkla", fg=self.colors["warning"])
            return

        # Kapalı bölge BFS; kenara değerse açık kabul et
        stack = [(x, y)]
        region = []
        seen = set()
        touches_border = False
        while stack:
            cx, cy = stack.pop()
            if (cx, cy) in seen:
                continue
            if not (0 <= cx < w and 0 <= cy < h):
                touches_border = True
                continue
            if bp[cx, cy] != 0:
                continue
            seen.add((cx, cy))
            region.append((cx, cy))
            if cx == 0 or cy == 0 or cx == w - 1 or cy == h - 1:
                touches_border = True
            stack.extend([(cx + 1, cy), (cx - 1, cy), (cx, cy + 1), (cx, cy - 1)])

        if touches_border:
            self.status_label.config(
                text="🪣 Alan çizgilerle kapalı değil — doldurulmadı",
                fg=self.colors["warning"],
            )
            return
        if not region:
            self.status_label.config(text="Doldurulacak alan yok", fg=self.colors["warning"])
            return

        if not self.fill_color:
            self._prompt_fill_color()
            if not self.fill_color:
                return

        fill_hex = self.fill_color.lstrip("#")
        try:
            if len(fill_hex) == 6:
                fr, fg, fb = int(fill_hex[0:2], 16), int(fill_hex[2:4], 16), int(fill_hex[4:6], 16)
            else:
                fr, fg, fb = 0, 0, 0
        except Exception:
            fr, fg, fb = 0, 0, 0
        fa = 255

        # Üst katmanda taşınabilir dolgu nesnesi (tabana boyama)
        xs = [p[0] for p in region]
        ys = [p[1] for p in region]
        min_x, max_x = min(xs), max(xs)
        min_y, max_y = min(ys), max(ys)
        bw, bh = max_x - min_x + 1, max_y - min_y + 1
        patch = Image.new("RGBA", (bw, bh), (0, 0, 0, 0))
        pp = patch.load()
        for px, py in region:
            pp[px - min_x, py - min_y] = (fr, fg, fb, fa)

        self.save_state()
        fill_obj = {
            "type": "fill_region",
            "layer": self.current_layer_id,
            "x1": float(min_x),
            "y1": float(min_y),
            "x2": float(max_x + 1),
            "y2": float(max_y + 1),
            "pil_image": patch,
            "opacity": self.opacity.get(),
            "color": self.fill_color,
        }
        self.objects.append(fill_obj)
        self.selected_obj = fill_obj
        self.selected_objs = [fill_obj]
        self._last_fill_region = None
        self.invalidate_cache()
        self.redraw()
        self.status_label.config(
            text=f"🪣 Dolgu eklendi (taşıyabilir) #{fr:02x}{fg:02x}{fb:02x}",
            fg=self.colors["success"],
        )

    def _flood_fill_bfs(self, img, x, y, target, replacement, thresh=28):
        w, h = img.size
        tr, tg, tb, ta = target[0], target[1], target[2], target[3] if len(target) > 3 else 255
        pixels = img.load()

        def match(px):
            if px is None:
                return False
            pr, pg, pb = px[0], px[1], px[2]
            pa = px[3] if len(px) > 3 else 255
            return (
                abs(pr - tr) <= thresh
                and abs(pg - tg) <= thresh
                and abs(pb - tb) <= thresh
                and abs(pa - ta) <= thresh
            )

        if not match(pixels[x, y]):
            return
        stack = [(x, y)]
        seen = set()
        while stack:
            cx, cy = stack.pop()
            if (cx, cy) in seen:
                continue
            if not (0 <= cx < w and 0 <= cy < h):
                continue
            if not match(pixels[cx, cy]):
                continue
            seen.add((cx, cy))
            pixels[cx, cy] = replacement
            stack.extend([(cx + 1, cy), (cx - 1, cy), (cx, cy + 1), (cx, cy - 1)])



    def _shape_edge_anchors(self, obj):
        """Şekil köşe + kenar orta noktaları (sayfa koordinatı)."""
        t = obj.get("type")
        if t in ("pen", "curve", "text", "arrow"):
            return []
        if t in ("image", "fill_region") or t in (
            "rect", "square", "circle", "triangle", "hexagon", "star", "callout"
        ):
            try:
                x1, y1 = float(obj.get("x1", 0)), float(obj.get("y1", 0))
                x2, y2 = float(obj.get("x2", x1)), float(obj.get("y2", y1))
            except Exception:
                return []
            # şekil noktaları varsa kenar ortaları
            try:
                sc = 1.0
                pts = self._shape_points(obj, x1, y1, x2, y2)
            except Exception:
                pts = []
            anchors = []
            if len(pts) >= 3:
                n = len(pts)
                for i in range(n):
                    anchors.append(pts[i])
                    ax, ay = pts[i]
                    bx, by = pts[(i + 1) % n]
                    anchors.append(((ax + bx) / 2, (ay + by) / 2))
            else:
                l, r = min(x1, x2), max(x1, x2)
                top, bot = min(y1, y2), max(y1, y2)
                cx, cy = (l + r) / 2, (top + bot) / 2
                anchors = [
                    (l, top), (cx, top), (r, top),
                    (r, cy), (r, bot), (cx, bot), (l, bot), (l, cy),
                ]
            return anchors
        return []

    def _all_visible_anchors(self):
        vis = {L["id"] for L in self.layers if L.get("visible")}
        out = []
        for obj in self.objects:
            if obj.get("layer", 0) not in vis:
                continue
            if obj.get("_drag_hide") or obj.get("_edit_hide"):
                continue
            for a in self._shape_edge_anchors(obj):
                out.append(a)
        return out

    def _snap_point(self, rx, ry, exclude_obj=None):
        """Noktayı sayfa kenarı / diğer nesne kenar ve köşelerine yapıştır."""
        if not self.original_image:
            return rx, ry
        thr = self.snap_threshold_px / max(self._vs(), 1e-6)
        pw, ph = self.original_image.size
        xs = [0.0, pw / 2.0, float(pw)]
        ys = [0.0, ph / 2.0, float(ph)]
        exclude = set()
        if exclude_obj is not None:
            exclude.add(id(exclude_obj))
            for m in self._group_members(exclude_obj):
                exclude.add(id(m))
        for o in self.objects:
            if id(o) in exclude:
                continue
            try:
                if o.get("points"):
                    for p in o["points"]:
                        xs.append(float(p[0]))
                        ys.append(float(p[1]))
                l, t, r, b = self._obj_bbox(o)
                xs.extend([l, (l + r) / 2.0, r])
                ys.extend([t, (t + b) / 2.0, b])
            except Exception:
                continue
        # waypoint anchors
        try:
            for ax, ay in self._collect_anchors():
                xs.append(ax)
                ys.append(ay)
        except Exception:
            pass
        best_x, bd_x = rx, thr
        for v in xs:
            d = abs(rx - v)
            if d < bd_x:
                best_x, bd_x = v, d
        best_y, bd_y = ry, thr
        for v in ys:
            d = abs(ry - v)
            if d < bd_y:
                best_y, bd_y = v, d
        nx = best_x if bd_x <= thr else rx
        ny = best_y if bd_y <= thr else ry
        gx = [nx] if bd_x <= thr else []
        gy = [ny] if bd_y <= thr else []
        try:
            if gx or gy:
                self._draw_guides(gx, gy)
            else:
                self._clear_guides()
        except Exception:
            pass
        return nx, ny

    def _snap_to_anchor(self, rx, ry, threshold=14):

        """En yakın bağlantı noktasına yapış (sayfa birimi)."""
        thr = threshold / max(self.scale, 0.05)
        best, bd = None, thr
        for ax, ay in self._all_visible_anchors():
            d = ((ax - rx) ** 2 + (ay - ry) ** 2) ** 0.5
            if d < bd:
                bd, best = d, (ax, ay)
        return best if best else (rx, ry)

    def _show_hover_anchors(self, near_x=None, near_y=None):
        """Şekil üstüne gelince bağlantı noktalarını göster."""
        self.canvas.delete("anchor_pt")
        # Yalnızca Ok Yol aracında waypoint göster
        if self.action != "arrow_path" and not getattr(self, "_arrow_path", None):
            self.canvas.delete("anchor_pt")
            self.canvas.delete("wp_guide")
            return
        sc = self._vs()
        vis = {L["id"] for L in self.layers if L.get("visible")}
        for obj in self.objects:
            if obj.get("layer", 0) not in vis:
                continue
            anchors = self._shape_edge_anchors(obj)
            if not anchors:
                continue
            # sadece fareye yakın şekil veya tümü (ok çizerken hepsi)
            show_all = self.action == "arrow_path" or getattr(self, "_arrow_path", None)
            if not show_all and near_x is not None:
                try:
                    x1, y1 = obj.get("x1", 0), obj.get("y1", 0)
                    x2, y2 = obj.get("x2", x1), obj.get("y2", y1)
                    pad = 20 / max(sc, 0.05)
                    if not (min(x1, x2) - pad <= near_x <= max(x1, x2) + pad and
                            min(y1, y2) - pad <= near_y <= max(y1, y2) + pad):
                        continue
                except Exception:
                    continue
            for ax, ay in anchors:
                cx = self.img_x + self.pan_x + ax * sc
                cy = self.img_y + self.pan_y + ay * sc
                r = 4
                self.canvas.create_oval(
                    cx - r, cy - r, cx + r, cy + r,
                    fill="#00e5ff", outline="white", width=1, tags="anchor_pt",
                )


    def _draw_waypoint_snap_guides(self, rx, ry):
        """Aktif waypoint hizasinda snap çizgileri (yatay/dikey)."""
        self.canvas.delete("wp_guide")
        anchors = self._all_visible_anchors()
        if getattr(self, "_arrow_path", None):
            anchors = list(anchors) + list(self._arrow_path)
        sc = self._vs()
        thr = 12 / max(sc, 0.05)
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        # fareye / hedefe yakın yatay-dikey kılavuzlar
        xs, ys = set(), set()
        for ax, ay in anchors:
            if abs(ax - rx) <= thr:
                xs.add(ax)
            if abs(ay - ry) <= thr:
                ys.add(ay)
        for ax in xs:
            cx = self.img_x + self.pan_x + ax * sc
            self.canvas.create_line(cx, 0, cx, ch, fill="#00e5ff", dash=(4, 3), width=1, tags="wp_guide")
        for ay in ys:
            cy = self.img_y + self.pan_y + ay * sc
            self.canvas.create_line(0, cy, cw, cy, fill="#00e5ff", dash=(4, 3), width=1, tags="wp_guide")
    def _finish_arrow_path(self):
        path = getattr(self, "_arrow_path", None) or []
        self._arrow_path = None
        self.canvas.delete("arrow_path_preview")
        self.canvas.delete("wp_guide")
        self.canvas.delete("anchor_pt")
        if len(path) < 2:
            self.status_label.config(text="Ok için en az 2 nokta gerekir", fg=self.colors["warning"])
            return
        self.save_state()
        xs = [p[0] for p in path]
        ys = [p[1] for p in path]
        self.objects.append({
            "type": "arrow",
            "layer": self.current_layer_id,
            "points": list(path),
            "x1": min(xs), "y1": min(ys),
            "x2": max(xs), "y2": max(ys),
            # uçlar (ok başı için)
            "ax1": path[0][0], "ay1": path[0][1],
            "ax2": path[-1][0], "ay2": path[-1][1],
            "color": self.outline_color,
            "width": self.thickness.get(),
            "opacity": self.opacity.get(),
        })
        self.redraw()
        self.status_label.config(text=f"↗ Ok yolu ({len(path)} nokta)", fg=self.colors["success"])

    def _cancel_arrow_path(self):
        self._arrow_path = None
        self.canvas.delete("arrow_path_preview")
        self.canvas.delete("wp_guide")
        self.canvas.delete("anchor_pt")

    def _shift_held(self, event):
        return bool(event.state & 0x0001)

    def _constrain_ortho_canvas(self, sx, sy, ex, ey):
        """Shift: yatay/dikey 90° (cursor yönüne göre)."""
        dx, dy = ex - sx, ey - sy
        if abs(dx) >= abs(dy):
            return sx, sy, ex, sy  # yatay
        return sx, sy, sx, ey  # dikey

    def _constrain_ortho_real(self, x1, y1, x2, y2):
        dx, dy = x2 - x1, y2 - y1
        if abs(dx) >= abs(dy):
            return x1, y1, x2, y1
        return x1, y1, x1, y2


    def _on_return_key(self, event=None):
        if getattr(self, "_arrow_path", None):
            self._finish_arrow_path()
            return
        self.apply_edge_crop()

    def _on_escape_key(self, event=None):
        if getattr(self, "_arrow_path", None):
            self._cancel_arrow_path()
            self.status_label.config(text="Ok iptal", fg=self.colors["warning"])
            return
        self.cancel_edge_crop()



    def _nudge_selected(self, dx, dy):
        """Ok tuşlarıyla taşı + snap kılavuzları."""
        targets = [o for o in (self.selected_objs or []) if o in self.objects and not self._is_locked(o)]
        if not targets and self.selected_obj and self.selected_obj in self.objects and not self._is_locked(self.selected_obj):
            targets = [self.selected_obj]
        if not targets:
            return
        if not getattr(self, "_nudge_saved", False):
            self.save_state()
            self._nudge_saved = True

        def _shift(o, sdx, sdy):
            if o.get("type") in ("pen", "curve", "arrow") and o.get("points"):
                o["points"] = [(p[0] + sdx, p[1] + sdy) for p in o["points"]]
            o["x1"] = o.get("x1", 0) + sdx
            o["y1"] = o.get("y1", 0) + sdy
            if "x2" in o:
                o["x2"] = o.get("x2", 0) + sdx
                o["y2"] = o.get("y2", 0) + sdy

        for o in targets:
            _shift(o, dx, dy)

        # Snap (birincil seçiliye göre)
        primary = self.selected_obj if self.selected_obj in targets else targets[0]
        sdx, sdy = self._snap_move(primary)
        if sdx or sdy:
            for o in targets:
                _shift(o, sdx, sdy)

        self.invalidate_cache()
        self.redraw()
        # kılavuzlar redraw sonrası tekrar
        self._snap_move(primary)
        self.draw_selection_ui()

    def _on_arrow_key(self, event, direction):
        if getattr(self, "_text_entry", None):
            return  # metin düzenlemede oklar caret için
        if not self.selected_obj and not self.selected_objs:
            return
        # basılı tutma hızlanması
        now = time.perf_counter()
        last = getattr(self, "_nudge_last_t", 0)
        count = getattr(self, "_nudge_count", 0)
        if now - last < 0.35:
            count += 1
        else:
            count = 0
        self._nudge_last_t = now
        self._nudge_count = count
        # adım: 1 → 2 → 5 → 12 → 24 (sayfa birimi)
        if count < 2:
            step = 1
        elif count < 6:
            step = 3
        elif count < 15:
            step = 8
        else:
            step = 18
        dx = dy = 0
        if direction == "Left":
            dx = -step
        elif direction == "Right":
            dx = step
        elif direction == "Up":
            dy = -step
        elif direction == "Down":
            dy = step
        self._nudge_selected(dx, dy)
        return "break"

    def on_press(self, event):
        if not self.original_image:
            return
        self.start_x, self.start_y = event.x, event.y
        rx, ry = self.to_real_coords(event.x, event.y)

        # Kenar kırpma tutamacı
        if self.edge_crop:
            h = self._hit_edge_handle(event.x, event.y)
            if h:
                self.edge_crop_handle = h
                self._edge_drag_start = (rx, ry, dict(self.edge_crop))
                return
            # tutamaç dışı tık: yok say
            return

        # crop: state release'te kaydedilir (büyük resimde press'te kasma olmasın)
        if self.action == "eyedropper":
            self.apply_eyedropper(rx, ry)
            return
        if self.action == "fill":
            self.apply_bucket_fill(rx, ry)
            return

        # Kırık ok (waypoint)
        if self.action == "arrow_path":
            snapped = self._snap_to_anchor(rx, ry, threshold=18)
            # waypoint'e tıklanınca oraya bağlan
            rx, ry = snapped
            if not getattr(self, "_arrow_path", None):
                self._arrow_path = [(rx, ry)]
                self.status_label.config(
                    text="↩ Ok Yol: tıkla=waypoint · waypoint'e yapışır · çift tık/Enter=bitir",
                    fg=self.colors["warning"],
                )
            else:
                lx, ly = self._arrow_path[-1]
                # 90° kilit; hedef zaten snap'li
                _, _, rx2, ry2 = self._constrain_ortho_real(lx, ly, rx, ry)
                # eğer snap noktası varsa ve yakınsa doğrudan bağla (ortho gevşet)
                if abs(rx - lx) < 0.5 or abs(ry - ly) < 0.5:
                    rx2, ry2 = rx, ry  # zaten hizalı
                else:
                    # snap noktasına L şeklinde bağlan (iki segment gerekebilir)
                    # tek segment ortho
                    rx2, ry2 = rx2, ry2
                if abs(rx2 - lx) > 0.5 or abs(ry2 - ly) > 0.5:
                    self._arrow_path.append((rx2, ry2))
                    # eğer hedef snap noktası ortho segmentte değilse köşe ekle
                    if abs(rx2 - rx) > 1 or abs(ry2 - ry) > 1:
                        self._arrow_path.append((rx, ry))
            self._preview_arrow_path(event.x, event.y, shift=True)
            self._show_hover_anchors(rx, ry)
            self._draw_waypoint_snap_guides(rx, ry)
            return

        if self.action in ["pen", "rect", "square", "circle", "triangle", "hexagon", "star", "callout", "curve", "arrow"]:
            self.save_state()

        if self.action == "move":
            self.resize_handle = None
            self._marquee = None
            self._multi_drag = False
            clicked = self.canvas.find_withtag("current")
            ctrl = bool(event.state & 0x0004)  # Control
            shift = bool(event.state & 0x0001)

            # --- KİLİT: önce tutamaç / nesne bul ---
            hit_obj = None
            tags = self.canvas.gettags(clicked[0]) if clicked else ()
            if clicked and "movable" in tags:
                for obj in self.objects:
                    if obj.get('id') == clicked[0]:
                        hit_obj = obj
                        break
            if hit_obj is None:
                try:
                    hit_obj = self._hit_object_at_canvas(event.x, event.y)
                except Exception:
                    hit_obj = None
            # kilitli asla seçilmesin
            if hit_obj and self._is_locked(hit_obj):
                hit_obj = None

            # Tutamaç: önce mesafeye göre (daha hassas)
            if self.handle_rects and self.selected_obj and not self._is_locked(self.selected_obj):
                best_h, best_d = None, 14  # px tolerans
                for h_type, h_id in self.handle_rects:
                    try:
                        bb = self.canvas.bbox(h_id)
                    except Exception:
                        continue
                    if not bb:
                        continue
                    hcx, hcy = (bb[0] + bb[2]) / 2, (bb[1] + bb[3]) / 2
                    d = ((event.x - hcx) ** 2 + (event.y - hcy) ** 2) ** 0.5
                    if d < best_d:
                        best_d, best_h = d, h_type
                if best_h is not None:
                    self.resize_handle = best_h
                    self.save_state()
                    self._drag_origin_sx = event.x
                    self._drag_origin_sy = event.y
                    self._drag_base = self._snapshot_obj_pos(self.selected_obj)
                    if best_h == 'se' and self.selected_obj and self.selected_obj.get('type') in ('text', 'textbox'):
                        self._text_resize_origin = (
                            event.x,
                            float(self.selected_obj.get('size', 24) or 24),
                        )
                    else:
                        self._text_resize_origin = None
                    if self.selected_obj and self.selected_obj not in self.selected_objs:
                        self.selected_objs = [self.selected_obj]
                    self.selected_objs = [o for o in self.selected_objs if not self._is_locked(o)]
                    # grup arkadaşlarını da ekle
                    if self.selected_obj:
                        extra = []
                        for m in self._group_members(self.selected_obj):
                            if m not in self.selected_objs and not self._is_locked(m):
                                extra.append(m)
                        self.selected_objs = self.selected_objs + extra
                    if not self.selected_objs:
                        self.resize_handle = None
                    else:
                        self._drag_bases = {id(o): self._snapshot_obj_pos(o) for o in self.selected_objs}
                        self._drag_base = self._drag_bases.get(id(self.selected_obj), self._drag_base)
                        for o in self.selected_objs:
                            o["_drag_hide"] = True
                        self.invalidate_cache()
                        self.redraw(exclude_selected=True)
                        self.draw_fast_drag_preview()
                        return

            if clicked:
                for h_type, h_id in self.handle_rects:
                    if clicked[0] == h_id:
                        # kilitliyse boyutlandırma yok
                        tgt = self.selected_obj or hit_obj
                        if tgt and self._is_locked(tgt):
                            self.status_label.config(text="🔒 Kilitli — boyut değiştirilemez", fg=self.colors["warning"])
                            self._multi_drag = False
                            self.resize_handle = None
                            self.draw_selection_ui()
                            return
                        self.resize_handle = h_type
                        self.save_state()
                        self._drag_origin_sx = event.x
                        self._drag_origin_sy = event.y
                        self._drag_base = self._snapshot_obj_pos(self.selected_obj)
                        if self.selected_obj and self.selected_obj not in self.selected_objs:
                            self.selected_objs = [self.selected_obj]
                        # kilitlileri taşıma setinden çıkar
                        self.selected_objs = [o for o in self.selected_objs if not self._is_locked(o)]
                        if self.selected_obj:
                            extra = []
                            for m in self._group_members(self.selected_obj):
                                if m not in self.selected_objs and not self._is_locked(m):
                                    extra.append(m)
                            self.selected_objs = self.selected_objs + extra
                        if not self.selected_objs:
                            self.resize_handle = None
                            return
                        self._drag_bases = {id(o): self._snapshot_obj_pos(o) for o in self.selected_objs}
                        self._drag_base = self._drag_bases.get(id(self.selected_obj), self._drag_base)
                        for o in self.selected_objs:
                            o["_drag_hide"] = True
                        self.invalidate_cache()
                        self.redraw(exclude_selected=True)
                        self.draw_fast_drag_preview()
                        return

            if hit_obj:
                if ctrl or shift:
                    cur = list(self.selected_objs)
                    if hit_obj in cur:
                        cur = [o for o in cur if o is not hit_obj]
                    else:
                        cur.extend(self._group_members(hit_obj))
                    self._set_selection(cur, expand_groups=True)
                else:
                    if hit_obj.get("group_id"):
                        self._set_selection(self._group_members(hit_obj), expand_groups=False)
                    elif hit_obj not in self.selected_objs or len(self.selected_objs) <= 1:
                        self._set_selection([hit_obj], expand_groups=False)

                # Kilitli → seçim yok
                if self._is_locked(hit_obj):
                    self._multi_drag = False
                    self.resize_handle = None
                    self.status_label.config(text="🔒 Kilitli — seçilemez (Ctrl+L ile aç)", fg=self.colors["warning"])
                    return

                if self.selected_obj:
                    self._suspend_prop_trace = True
                    try:
                        obj = self.selected_obj
                        if obj.get('color'):
                            self.outline_color = obj.get('color', '#e94560')
                            try:
                                if getattr(self, "btn_outline_color", None):
                                    self.btn_outline_color.config(bg=self.outline_color)
                            except Exception:
                                pass
                        if obj.get('opacity') is not None:
                            self.opacity.set(obj['opacity'])
                        if obj['type'] in ('text', 'textbox'):
                            self.font_size.set(obj.get('size', 24))
                        elif obj['type'] != 'image':
                            self.thickness.set(obj.get('width', 3))
                            if obj.get('label') is not None:
                                self.font_size.set(obj.get('label_size', self.font_size.get()))
                            if obj.get('fill'):
                                self.fill_color = obj['fill']
                                self.btn_fill_color.config(bg=obj['fill'], text="Renk")
                            else:
                                self.fill_color = ""
                                self.btn_fill_color.config(bg="gray", text="Yok")
                    finally:
                        self._suspend_prop_trace = False

                    # Taşınacaklar: yalnızca kilitli OLMAYANLAR
                    move_set = []
                    for o in list(self.selected_objs):
                        for m in self._group_members(o):
                            if m not in move_set:
                                move_set.append(m)
                    move_set = [o for o in move_set if not self._is_locked(o)]
                    if not move_set:
                        self._multi_drag = False
                        self.resize_handle = None
                        self.status_label.config(text="🔒 Kilitli — taşınamaz", fg=self.colors["warning"])
                        self.draw_selection_ui()
                        return

                    self.save_state()
                    self._drag_origin_sx = event.x
                    self._drag_origin_sy = event.y
                    self.selected_objs = move_set
                    if self.selected_obj not in self.selected_objs:
                        self.selected_obj = self.selected_objs[-1]
                    self._drag_bases = {id(o): self._snapshot_obj_pos(o) for o in self.selected_objs}
                    for o in self.selected_objs:
                        if o.get("type") in ("text", "textbox"):
                            self._drag_bases[id(o)]["size"] = o.get("size", 24)
                    self._multi_drag = True
                    self.resize_handle = None  # taşıma, büyütme değil
                    for o in self.selected_objs:
                        o["_drag_hide"] = True
                    self.canvas.delete("drag_preview")
                    self.canvas.delete("text_size_preview")
                    self.drag_items = []
                    self.invalidate_cache()
                    # bitmap'ten seçilileri tamamen çıkar (çift yazı önler)
                    self.redraw(exclude_selected=True)
                    self._drag_preview_ts = 0
                    self.draw_fast_drag_preview()
                    try:
                        self.canvas.tag_raise("drag_preview")
                        self.canvas.tag_raise("selection_ui")
                    except Exception:
                        pass
            else:
                # boş alan → marquee (toplu kutu seçimi)
                if not ctrl and not shift:
                    self._set_selection([])
                self._marquee = [event.x, event.y, event.x, event.y]
                self._marquee_additive = ctrl or shift

            self.draw_selection_ui()
            n = len(self.selected_objs)
            if n > 1:
                gids = {o.get("group_id") for o in self.selected_objs if o.get("group_id")}
                if len(gids) == 1:
                    gid = next(iter(gids))
                    gname = self.groups.get(gid, {}).get("name", f"Grup {gid}")
                    self.status_label.config(text=f"🧩 {gname}: {n} üye — birlikte taşınır", fg=self.colors["success"])
                else:
                    self.status_label.config(text=f"☑ {n} nesne seçili — sürükleyerek taşı", fg=self.colors["success"])

            if getattr(self, "_crop_after_select", False) and self.selected_obj and self.selected_obj.get("type") == "image":
                self._crop_after_select = False
                self.start_image_edge_crop(self.selected_obj)

        elif self.action == "text":
            hit = None
            try:
                hit = self._hit_object_at_canvas(event.x, event.y)
            except Exception:
                pass
            if hit and hit.get("type") in ("text", "textbox") and not self._is_locked(hit):
                self.edit_text_object(hit)
            else:
                self.start_inline_text(event.x, event.y, rx, ry)

        elif self.action == "pen":
            self.current_pen_obj = {
                'type': 'pen',
                'layer': self.current_layer_id,
                'points': [(rx, ry)],
                'color': self.outline_color,
                'width': self.thickness.get(),
                'opacity': self.opacity.get()
            }
            self.objects.append(self.current_pen_obj)

    def on_motion(self, event):
        """Hover: yalnızca Ok Yol aracında bağlantı noktaları."""
        if not self.original_image:
            return
        if getattr(self, "is_panning", False) or getattr(self, "_multi_drag", False):
            return
        if self.action != "arrow_path" and not getattr(self, "_arrow_path", None):
            self.canvas.delete("anchor_pt")
            self.canvas.delete("wp_guide")
            return
        try:
            rx, ry = self.to_real_coords(event.x, event.y)
        except Exception:
            return
        self._show_hover_anchors(rx, ry)
        if getattr(self, "_arrow_path", None) and len(self._arrow_path) >= 1:
            self._preview_arrow_path(event.x, event.y, shift=True)
            self._draw_waypoint_snap_guides(rx, ry)


    def _preview_arrow_path(self, cx, cy, shift=True):
        self.canvas.delete("arrow_path_preview")
        path = list(self._arrow_path)
        try:
            rx, ry = self.to_real_coords(cx, cy)
        except Exception:
            return
        rx, ry = self._snap_to_anchor(rx, ry)
        if path:
            lx, ly = path[-1]
            if shift or True:  # ok için varsayılan 90°
                _, _, rx, ry = self._constrain_ortho_real(lx, ly, rx, ry)
            path = path + [(rx, ry)]
        sc = self._vs()
        w = max(1, int(self.thickness.get() * sc))
        flat = []
        for px, py in path:
            flat.extend([self.img_x + self.pan_x + px * sc, self.img_y + self.pan_y + py * sc])
        if len(flat) >= 4:
            self.canvas.create_line(
                *flat, fill=self.outline_color, width=w,
                arrow=tk.LAST, smooth=False, tags="arrow_path_preview",
            )

    def on_drag(self, event):

        if self.is_panning or not self.original_image:
            return

        # Kenar tutamacı sürükleme
        if self.edge_crop and self.edge_crop_handle and getattr(self, "_edge_drag_start", None):
            rx, ry = self.to_real_coords(event.x, event.y)
            _, _, base = self._edge_drag_start
            h = self.edge_crop_handle
            ec = self.edge_crop
            min_size = 8.0
            l, t, r, b = base["l"], base["t"], base["r"], base["b"]
            if "w" in h:
                l = min(rx, r - min_size)
            if "e" in h:
                r = max(rx, l + min_size)
            if "n" in h:
                t = min(ry, b - min_size)
            if "s" in h:
                b = max(ry, t + min_size)
            if ec["mode"] == "page":
                pw, ph = self.original_image.size
                l = max(0.0, min(l, pw - min_size))
                t = max(0.0, min(t, ph - min_size))
                r = max(l + min_size, min(float(pw), r))
                b = max(t + min_size, min(float(ph), b))
            elif ec["mode"] == "page_resize":
                # serbest: büyütme/küçültme (çok aşırıya kaçma)
                max_dim = 20000.0
                l = max(-max_dim, l)
                t = max(-max_dim, t)
                r = min(max_dim, max(l + min_size, r))
                b = min(max_dim, max(t + min_size, b))
            ec["l"], ec["t"], ec["r"], ec["b"] = l, t, r, b
            # image mode: canlı bbox önizleme
            if ec["mode"] == "image" and ec.get("obj"):
                ec["obj"]["x1"], ec["obj"]["y1"] = l, t
                ec["obj"]["x2"], ec["obj"]["y2"] = r, b
            self.draw_edge_crop_ui()
            return

        if not self.action:
            return

        # Şekil önizlemesi her karede yenilenir; fırça çizgileri birikmeli (silinmez)
        if self.action != "pen":
            for item in self.temp_items:
                self.canvas.delete(item)
            self.temp_items.clear()

        if self.action == "move" and self._marquee is not None:
            self._marquee[2], self._marquee[3] = event.x, event.y
            self.canvas.delete("marquee")
            x1, y1, x2, y2 = self._marquee
            self.canvas.create_rectangle(
                x1, y1, x2, y2,
                outline="#00e5ff", dash=(4, 2), width=1, tags="marquee"
            )
            return

        if self.action == "move" and getattr(self, "_multi_drag", False) and not self.resize_handle:
            # Kilitli nesne asla hareket etmesin
            if self.selected_obj and self._is_locked(self.selected_obj):
                self._multi_drag = False
                return
            self.selected_objs = [o for o in (self.selected_objs or []) if not self._is_locked(o)]
            if not self.selected_objs:
                self._multi_drag = False
                return
            total_dx = (event.x - self._drag_origin_sx) / self._vs()
            total_dy = (event.y - self._drag_origin_sy) / self._vs()
            bases = getattr(self, "_drag_bases", {})
            for o in self.selected_objs:
                base = bases.get(id(o))
                if not base:
                    continue
                if o.get("type") in ("pen", "curve", "arrow") and "points" in base and base.get("points"):
                    o["points"] = [(p[0] + total_dx, p[1] + total_dy) for p in base.get("points", [])]
                    if "x1" in base:
                        o["x1"] = base["x1"] + total_dx
                        o["y1"] = base["y1"] + total_dy
                        o["x2"] = base.get("x2", base["x1"]) + total_dx
                        o["y2"] = base.get("y2", base["y1"]) + total_dy
                else:
                    o["x1"] = base["x1"] + total_dx
                    o["y1"] = base["y1"] + total_dy
                    if "x2" in base:
                        o["x2"] = base["x2"] + total_dx
                        o["y2"] = base["y2"] + total_dy
            if self.selected_obj and not self._is_locked(self.selected_obj):
                sdx, sdy = self._snap_move(self.selected_obj)
                if sdx or sdy:
                    for o in self.selected_objs:
                        if o.get("type") in ("pen", "curve") and o.get("points"):
                            o["points"] = [(p[0] + sdx, p[1] + sdy) for p in o["points"]]
                        o["x1"] = o.get("x1", 0) + sdx
                        o["y1"] = o.get("y1", 0) + sdy
                        if "x2" in o:
                            o["x2"] = o.get("x2", 0) + sdx
                            o["y2"] = o.get("y2", 0) + sdy
            self.draw_fast_drag_preview()
            return

        if self.action == "move" and self.selected_obj:
            rx, ry = self.to_real_coords(event.x, event.y)

            if self.resize_handle:
                if self._is_locked(self.selected_obj):
                    self.resize_handle = None
                    return
                obj = self.selected_obj
                self._last_event = event
                targets = [o for o in (self.selected_objs or [obj]) if o and not self._is_locked(o)]
                if obj and obj not in targets:
                    targets.append(obj)
                bases = getattr(self, "_drag_bases", None) or {}
                if not bases:
                    bases = {id(o): self._snapshot_obj_pos(o) for o in targets}
                    self._drag_bases = bases
                # grup veya çoklu: birlikte ölçekle
                if len(targets) > 1 and self.resize_handle in ("nw", "ne", "sw", "se"):
                    self._scale_objects_uniform(targets, bases, self.resize_handle, rx, ry)
                    self._snap_group_bbox(targets, self.resize_handle)
                elif obj['type'] in ['rect', 'square', 'circle', 'triangle', 'hexagon', 'star', 'callout', 'image', 'fill_region']:
                    if self.resize_handle == 'nw':
                        obj['x1'], obj['y1'] = rx, ry
                    elif self.resize_handle == 'ne':
                        obj['x2'], obj['y1'] = rx, ry
                    elif self.resize_handle == 'sw':
                        obj['x1'], obj['y2'] = rx, ry
                    elif self.resize_handle == 'se':
                        obj['x2'], obj['y2'] = rx, ry
                elif obj['type'] == 'arrow':
                    hx = self.resize_handle
                    if self._shift_held(event) and hx in ('start', 'end'):
                        if hx == 'start':
                            _, _, rx, ry = self._constrain_ortho_real(obj.get('x2', rx), obj.get('y2', ry), rx, ry)
                        else:
                            _, _, rx, ry = self._constrain_ortho_real(obj.get('x1', rx), obj.get('y1', ry), rx, ry)
                    # uç / ara nokta snap
                    if hx in ('start', 'end') or (isinstance(hx, str) and hx.startswith('apt')):
                        rx, ry = self._snap_point(rx, ry, exclude_obj=obj)
                    pts = obj.get('points')
                    if isinstance(hx, str) and hx.startswith('apt'):
                        try:
                            pi = int(hx[3:])
                        except Exception:
                            pi = -1
                        if pts and 0 <= pi < len(pts):
                            if self._shift_held(event):
                                if pi > 0:
                                    lx, ly = pts[pi - 1]
                                    _, _, rx, ry = self._constrain_ortho_real(lx, ly, rx, ry)
                                elif pi + 1 < len(pts):
                                    lx, ly = pts[pi + 1]
                                    _, _, rx, ry = self._constrain_ortho_real(lx, ly, rx, ry)
                            pts[pi] = (rx, ry)
                            obj['points'] = pts
                            obj['x1'] = min(p[0] for p in pts)
                            obj['y1'] = min(p[1] for p in pts)
                            obj['x2'] = max(p[0] for p in pts)
                            obj['y2'] = max(p[1] for p in pts)
                    elif hx == 'start':
                        obj['x1'], obj['y1'] = rx, ry
                        if pts and len(pts) >= 1:
                            pts[0] = (rx, ry)
                            obj['points'] = pts
                    elif hx == 'end':
                        obj['x2'], obj['y2'] = rx, ry
                        if pts and len(pts) >= 1:
                            pts[-1] = (rx, ry)
                            obj['points'] = pts
                elif obj['type'] in ('text', 'textbox') and self.resize_handle == 'se':
                    base = getattr(self, '_drag_base', None) or {}
                    origin_size = float(base.get('size', obj.get('size', 24)) or 24)
                    origin = getattr(self, '_text_resize_origin', None)
                    if not origin or not isinstance(origin, (tuple, list)) or len(origin) < 2:
                        self._text_resize_origin = (event.x, origin_size)
                        origin = self._text_resize_origin
                    ox, osz = float(origin[0]), float(origin[1])
                    dx = (event.x - ox) / max(self._vs(), 0.01)
                    new_size = int(max(8, min(200, round(osz + dx * 0.15))))
                    obj['size'] = new_size
                    self._suspend_prop_trace = True
                    try:
                        self.font_size.set(new_size)
                    finally:
                        self._suspend_prop_trace = False

                # kenar snap (boyutlandırma)
                if self.resize_handle in ("nw", "ne", "sw", "se") and obj.get("type") in (
                    "rect", "square", "circle", "triangle", "hexagon", "star", "callout", "image", "fill_region"
                ):
                    self._snap_resize_edges(obj, self.resize_handle)
                self.draw_fast_drag_preview()
                return

            # Toplam delta (press'ten beri) — snap takılması olmasın
            if not getattr(self, '_drag_base', None):
                self._drag_origin_sx = event.x
                self._drag_origin_sy = event.y
                self._drag_base = self._snapshot_obj_pos(self.selected_obj)
                self.selected_obj["_drag_hide"] = True
                self.invalidate_cache()
                self.redraw(exclude_selected=True)
            total_dx = (event.x - self._drag_origin_sx) / self._vs()
            total_dy = (event.y - self._drag_origin_sy) / self._vs()
            base = self._drag_base

            if self.selected_obj.get('type') in ('pen', 'curve') and base.get('points') is not None:
                self.selected_obj['points'] = [
                    (p[0] + total_dx, p[1] + total_dy) for p in base['points']
                ]
                if 'x1' in base:
                    self.selected_obj['x1'] = base['x1'] + total_dx
                    self.selected_obj['y1'] = base['y1'] + total_dy
                    self.selected_obj['x2'] = base.get('x2', base['x1']) + total_dx
                    self.selected_obj['y2'] = base.get('y2', base['y1']) + total_dy
            else:
                self.selected_obj['x1'] = base['x1'] + total_dx
                self.selected_obj['y1'] = base['y1'] + total_dy
                if 'x2' in base:
                    self.selected_obj['x2'] = base['x2'] + total_dx
                    self.selected_obj['y2'] = base['y2'] + total_dy

            # Snap (fırça dahil)
            sdx, sdy = self._snap_move(self.selected_obj)
            if sdx or sdy:
                if self.selected_obj.get('type') in ('pen', 'curve') and self.selected_obj.get('points'):
                    self.selected_obj['points'] = [
                        (p[0] + sdx, p[1] + sdy) for p in self.selected_obj['points']
                    ]
                self.selected_obj['x1'] = self.selected_obj.get('x1', 0) + sdx
                self.selected_obj['y1'] = self.selected_obj.get('y1', 0) + sdy
                if 'x2' in self.selected_obj:
                    self.selected_obj['x2'] += sdx
                    self.selected_obj['y2'] += sdy

            self.draw_fast_drag_preview()

        elif self.action == "pen":
            if not getattr(self, 'current_pen_obj', None):
                return
            rx, ry = self.to_real_coords(event.x, event.y)
            ex, ey = event.x, event.y
            if self._shift_held(event):
                sx, sy, ex, ey = self._constrain_ortho_canvas(self.start_x, self.start_y, event.x, event.y)
                rx, ry = self.to_real_coords(ex, ey)
            self.current_pen_obj['points'].append((rx, ry))
            w = max(1, int(self.thickness.get() * self._vs()))
            self.temp_items.append(
                self.canvas.create_line(
                    self.start_x, self.start_y, ex, ey,
                    fill=self.outline_color, width=w,
                    capstyle=tk.ROUND, joinstyle=tk.ROUND,
                    tags="pen_stroke"
                )
            )
            self.start_x, self.start_y = ex, ey

        elif self.action == "crop":
            cw = self.canvas.winfo_width()
            ch = self.canvas.winfo_height()
            left, right = min(self.start_x, event.x), max(self.start_x, event.x)
            top, bottom = min(self.start_y, event.y), max(self.start_y, event.y)
            self.temp_items.extend([
                self.canvas.create_rectangle(
                    0, 0, cw, top,
                    fill="#1a1a2e", stipple="gray50", outline=""
                ),
                self.canvas.create_rectangle(
                    0, bottom, cw, ch,
                    fill="#1a1a2e", stipple="gray50", outline=""
                ),
                self.canvas.create_rectangle(
                    0, top, left, bottom,
                    fill="#1a1a2e", stipple="gray50", outline=""
                ),
                self.canvas.create_rectangle(
                    right, top, cw, bottom,
                    fill="#1a1a2e", stipple="gray50", outline=""
                ),
                self.canvas.create_rectangle(
                    left, top, right, bottom,
                    outline=self.colors["accent"], dash=(4,4), width=2
                )
            ])

        elif self.action == "zoom_region":
            left, right = min(self.start_x, event.x), max(self.start_x, event.x)
            top, bottom = min(self.start_y, event.y), max(self.start_y, event.y)
            self.temp_items.append(
                self.canvas.create_rectangle(
                    left, top, right, bottom,
                    outline="#00e5ff", dash=(6, 3), width=2, tags="zoom_region_rect"
                )
            )
            # Yarı saydam dolgu
            self.temp_items.append(
                self.canvas.create_rectangle(
                    left, top, right, bottom,
                    outline="", fill="#00e5ff", stipple="gray25", tags="zoom_region_rect"
                )
            )

        elif self.action == "arrow_path":
            self._preview_arrow_path(event.x, event.y, shift=True)
            try:
                rx, ry = self.to_real_coords(event.x, event.y)
                self._draw_waypoint_snap_guides(rx, ry)
            except Exception:
                pass
            return

        elif self.action in ["rect", "square", "circle", "triangle", "hexagon", "star", "callout", "curve", "arrow"]:
            w = max(1, int(self.thickness.get() * self.scale))
            sx, sy, ex, ey = self.start_x, self.start_y, event.x, event.y
            if self._shift_held(event) and self.action in ("arrow", "curve", "rect", "callout"):
                sx, sy, ex, ey = self._constrain_ortho_canvas(sx, sy, ex, ey)
            if self.action == "square":
                side = max(abs(ex - sx), abs(ey - sy))
                ex = sx + (side if ex >= sx else -side)
                ey = sy + (side if ey >= sy else -side)
            if self.action == "arrow":
                self.temp_items.append(
                    self.canvas.create_line(sx, sy, ex, ey, arrow=tk.LAST, fill=self.outline_color, width=w)
                )
            elif self.action == "circle":
                self.temp_items.append(
                    self.canvas.create_oval(sx, sy, ex, ey, outline=self.outline_color, fill=self.fill_color or "", width=w)
                )
            elif self.action == "curve":
                mx, my = (sx + ex) / 2, (sy + ey) / 2 - 40
                self.temp_items.append(
                    self.canvas.create_line(sx, sy, mx, my, ex, ey, smooth=True, fill=self.outline_color, width=w)
                )
            else:
                # polygon önizleme
                fake = {"type": self.action, "rotation": 0}
                # canvas coords as x1,y1,x2,y2
                pts = self._shape_points(fake, sx, sy, ex, ey)
                flat = [c for p in pts for c in p]
                if len(flat) >= 6:
                    self.temp_items.append(
                        self.canvas.create_polygon(flat, outline=self.outline_color, fill=self.fill_color or "", width=w)
                    )

    def on_release(self, event):
        if self.is_panning:
            self.is_panning = False
            self.canvas.config(cursor="cross" if self.action != "move" else "fleur")
            return

        if self.edge_crop and self.edge_crop_handle:
            self.edge_crop_handle = None
            self._edge_drag_start = None
            self.draw_edge_crop_ui()
            return

        # Marquee toplu seçim
        if self.action == "move" and self._marquee is not None:
            x1, y1, x2, y2 = self._marquee
            self.canvas.delete("marquee")
            self._marquee = None
            left, right = min(x1, x2), max(x1, x2)
            top, bottom = min(y1, y2), max(y1, y2)
            if right - left > 3 and bottom - top > 3:
                hits = []
                for obj in self.objects:
                    if self._is_locked(obj):
                        continue
                    oid = obj.get("id")
                    if not oid:
                        continue
                    try:
                        bx1, by1, bx2, by2 = self.canvas.bbox(oid)
                    except Exception:
                        continue
                    if bx2 < left or bx1 > right or by2 < top or by1 > bottom:
                        continue
                    hits.append(obj)
                if getattr(self, "_marquee_additive", False):
                    cur = list(self.selected_objs)
                    for h in hits:
                        if h not in cur:
                            cur.append(h)
                    self._set_selection(cur)
                else:
                    self._set_selection(hits)
                n = len(self.selected_objs)
                self.status_label.config(
                    text=f"☑ {n} nesne seçildi" if n else "Seçim yok",
                    fg=self.colors["success"] if n else self.colors["warning"],
                )
            self._multi_drag = False
            self.draw_selection_ui()
            return

        self._multi_drag = False
        # Sürükleme gizlemesini kaldır
        for o in self.objects:
            if o.get("_drag_hide"):
                o.pop("_drag_hide", None)

        if not self.original_image or not self.action:
            return

        self._clear_guides()
        self.resize_handle = None
        for item in self.temp_items:
            self.canvas.delete(item)
        self.temp_items.clear()

        if self.action in ["move", "pen"]:
            for item in self.drag_items:
                try:
                    self.canvas.delete(item)
                except Exception:
                    pass
            self.drag_items = []
            self.canvas.delete("drag_preview")
            self.canvas.delete("text_size_preview")
            self.canvas.delete("pen_stroke")
            self.canvas.delete("selection_ui")
            self._drag_photos = []
            for item in self.temp_items:
                try:
                    self.canvas.delete(item)
                except Exception:
                    pass
            self.temp_items = []
            self.current_pen_obj = None
            self._drag_base = None
            self._drag_bases = {}
            self._text_resize_origin = None
            self._multi_drag = False
            # tüm gizleme bayraklarını temizle
            for o in self.objects:
                o.pop("_drag_hide", None)
                o.pop("_edit_hide", None)
            self.invalidate_cache()
            # tam sayfa render (önizleme değil)
            self.redraw(exclude_selected=False)
            self.draw_selection_ui()
            # bir kare sonra ikinci render (önbellek / sıra sorunlarını giderir)
            self.root.after(10, self._finalize_move_render)
            return

        rx1, ry1 = self.to_real_coords(self.start_x, self.start_y)
        rx2, ry2 = self.to_real_coords(event.x, event.y)
        if self._shift_held(event) and self.action in ("arrow", "curve", "rect", "callout"):
            rx1, ry1, rx2, ry2 = self._constrain_ortho_real(rx1, ry1, rx2, ry2)
        left, right = min(rx1, rx2), max(rx1, rx2)
        top, bottom = min(ry1, ry2), max(ry1, ry2)

        if self.action in ["rect", "square", "circle", "triangle", "hexagon", "star", "callout"] and right > left and bottom > top:
            if self.action == "square":
                side = max(right - left, bottom - top)
                right, bottom = left + side, top + side
            self.objects.append({
                'type': self.action,
                'layer': self.current_layer_id,
                'x1': left, 'y1': top,
                'x2': right, 'y2': bottom,
                'color': self.outline_color,
                'fill': self.fill_color,
                'width': self.thickness.get(),
                'opacity': self.opacity.get(),
                'rotation': 0,
            })
            self.redraw()

        elif self.action == "curve" and (rx1 != rx2 or ry1 != ry2):
            mx = (rx1 + rx2) / 2
            my = (ry1 + ry2) / 2 - abs(rx2 - rx1) * 0.2
            self.objects.append({
                'type': 'curve',
                'layer': self.current_layer_id,
                'points': [(rx1, ry1), (mx, my), (rx2, ry2)],
                'x1': min(rx1, rx2, mx), 'y1': min(ry1, ry2, my),
                'x2': max(rx1, rx2, mx), 'y2': max(ry1, ry2, my),
                'color': self.outline_color,
                'width': self.thickness.get(),
                'opacity': self.opacity.get(),
                'rotation': 0,
            })
            self.redraw()

        elif self.action == "arrow" and (rx1 != rx2 or ry1 != ry2):
            self.objects.append({
                "type": "arrow",
                "layer": self.current_layer_id,
                "x1": rx1, "y1": ry1,
                "x2": rx2, "y2": ry2,
                "color": self.outline_color,
                "width": self.thickness.get(),
                "opacity": self.opacity.get(),
            })
            self.redraw()

        elif self.action == "crop" and right > left and bottom > top:
            pw, ph = self.original_image.size
            left_i = max(0, min(pw - 1, int(left)))
            top_i = max(0, min(ph - 1, int(top)))
            right_i = max(left_i + 1, min(pw, int(right)))
            bottom_i = max(top_i + 1, min(ph, int(bottom)))
            if right_i - left_i < 2 or bottom_i - top_i < 2:
                self.status_label.config(text="Kırpma alanı çok küçük", fg=self.colors["warning"])
                return

            # Snapshot BEFORE mutate (undo için)
            self.save_state()
            self.original_image = self.original_image.crop((left_i, top_i, right_i, bottom_i))
            self.invalidate_cache()
            for obj in self.objects:
                if 'points' in obj:
                    obj['points'] = [(p[0] - left_i, p[1] - top_i) for p in obj['points']]
                else:
                    obj['x1'] = obj.get('x1', 0) - left_i
                    obj['y1'] = obj.get('y1', 0) - top_i
                    if obj['type'] in ['rect', 'circle', 'triangle', 'arrow', 'image', 'fill_region']:
                        obj['x2'] = obj.get('x2', 0) - left_i
                        obj['y2'] = obj.get('y2', 0) - top_i

            self.pan_x = 0
            self.pan_y = 0
            cw = self.canvas.winfo_width()
            ch = self.canvas.winfo_height()
            if cw > 1 and ch > 1:
                self.scale = min((cw - 40) / max(1, self.original_image.width),
                               (ch - 40) / max(1, self.original_image.height))
            self._initial_scale = self.scale
            self.action = "move"
            self.redraw()
            self.status_label.config(
                text=f"✂ Kırpıldı — {self.original_image.width}×{self.original_image.height}",
                fg=self.colors["success"]
            )

        elif self.action == "zoom_region" and right > left and bottom > top:
            # left/top/right/bottom zaten sayfa koordinatı
            region_w = max(1e-3, right - left)
            region_h = max(1e-3, bottom - top)

            cw = self.canvas.winfo_width()
            ch = self.canvas.winfo_height()
            if cw <= 1 or ch <= 1:
                return

            margin = 20
            fit = min((cw - margin) / region_w, (ch - margin) / region_h)
            fit = max(0.05, min(fit, self._max_scale()))

            self.scale = fit
            self.invalidate_cache()

            # Bölge ortası ekran ortasında olsun
            cx = (left + right) / 2.0
            cy = (top + bottom) / 2.0
            page_w = self.original_image.width * self.scale
            page_h = self.original_image.height * self.scale
            self.img_x = max(0, int((cw - page_w) // 2))
            self.img_y = max(0, int((ch - page_h) // 2))
            self.pan_x = cw / 2.0 - self.img_x - cx * self.scale
            self.pan_y = ch / 2.0 - self.img_y - cy * self.scale

            self.redraw()
            self.status_label.config(
                text=f"🔍 Bölge zoom — ölçek {self.scale:.0%}",
                fg=self.colors["success"]
            )
            # Araç seçili kalsın; tekrar sürükleyerek başka bölgeye zoom yapılabilir

    # --- DIŞA AKTARIM (EXPORT) ---
    def render_for_export(self):
        """Yüksek kalite kayıt - üst üste şeffaflık korunur"""
        bg = self.original_image.copy()
        if bg.mode != "RGBA":
            bg = bg.convert("RGBA")

        result = bg
        visible_layers = [l["id"] for l in self.layers if l["visible"]]

        for obj in self.objects:
            if obj.get('layer', 0) not in visible_layers:
                continue

            op = obj.get('opacity', 100)
            outline_rgba = self.hex_to_rgba(obj['color'], op) if obj.get('color') else (0, 0, 0, 0)
            fill_rgba = self.hex_to_rgba(obj.get('fill'), op) if obj.get('fill') else None
            w = max(1, int(obj.get('width', 1)))

            layer = Image.new("RGBA", result.size, (0, 0, 0, 0))
            draw = ImageDraw.Draw(layer, "RGBA")

            if obj['type'] in ('text', 'textbox'):
                result = self._draw_text_with_bg(
                    result, obj, obj.get('x1', 0), obj.get('y1', 0), 1.0, outline_rgba,
                )
                continue
            elif obj['type'] == 'circle' and not obj.get('rotation') and not obj.get('flip_h') and not obj.get('flip_v'):
                draw.ellipse([obj['x1'], obj['y1'], obj['x2'], obj['y2']], outline=outline_rgba, fill=fill_rgba, width=w)
                if obj.get('label'):
                    try:
                        self._draw_shape_label(
                            draw, obj,
                            obj['x1'], obj['y1'], obj['x2'], obj['y2'],
                            sc=1.0, opacity=op,
                        )
                    except Exception:
                        pass
            elif obj['type'] in ('rect', 'square', 'circle', 'triangle', 'hexagon', 'star', 'callout'):
                pts = self._shape_points(obj, obj['x1'], obj['y1'], obj['x2'], obj['y2'])
                if len(pts) >= 3:
                    draw.polygon(pts, outline=outline_rgba, fill=fill_rgba, width=w)
                if obj.get('label'):
                    try:
                        self._draw_shape_label(
                            draw, obj,
                            obj['x1'], obj['y1'], obj['x2'], obj['y2'],
                            sc=1.0, opacity=op,
                        )
                    except Exception:
                        pass
            elif obj['type'] == 'curve' and len(obj.get('points', [])) >= 2:
                pts = obj['points']
                if len(pts) == 2:
                    draw.line(pts, fill=outline_rgba, width=w)
                else:
                    p0, p1, p2 = pts[0], pts[1], pts[2]
                    samples = []
                    for i in range(33):
                        tt = i / 32.0
                        ax = (1 - tt) ** 2 * p0[0] + 2 * (1 - tt) * tt * p1[0] + tt ** 2 * p2[0]
                        ay = (1 - tt) ** 2 * p0[1] + 2 * (1 - tt) * tt * p1[1] + tt ** 2 * p2[1]
                        samples.append((ax, ay))
                    draw.line(samples, fill=outline_rgba, width=w, joint="curve")
            elif obj['type'] == 'arrow':
                pts = obj.get('points')
                if pts and len(pts) >= 2:
                    draw.line(pts, fill=outline_rgba, width=w, joint="curve")
                    ax1, ay1 = pts[-2]
                    ax2, ay2 = pts[-1]
                else:
                    ax1, ay1, ax2, ay2 = obj['x1'], obj['y1'], obj['x2'], obj['y2']
                    draw.line([ax1, ay1, ax2, ay2], fill=outline_rgba, width=w)
                angle = math.atan2(ay2 - ay1, ax2 - ax1)
                al, aa = w * 3 + 10, math.pi / 6
                draw.polygon([
                    ax2, ay2,
                    ax2 - al * math.cos(angle - aa), ay2 - al * math.sin(angle - aa),
                    ax2 - al * math.cos(angle + aa), ay2 - al * math.sin(angle + aa),
                ], fill=outline_rgba)
                angle = math.atan2(obj['y2'] - obj['y1'], obj['x2'] - obj['x1'])
                al, aa = w * 3 + 10, math.pi / 6
                draw.polygon([
                    obj['x2'], obj['y2'],
                    obj['x2'] - al * math.cos(angle - aa),
                    obj['y2'] - al * math.sin(angle - aa),
                    obj['x2'] - al * math.cos(angle + aa),
                    obj['y2'] - al * math.sin(angle + aa)
                ], fill=outline_rgba)
            elif obj['type'] in ('image', 'fill_region') and obj.get('pil_image') is not None:
                try:
                    x1, y1, x2, y2 = obj['x1'], obj['y1'], obj['x2'], obj['y2']
                    iw = max(1, int(abs(x2 - x1)))
                    ih = max(1, int(abs(y2 - y1)))
                    resized = obj['pil_image'].resize((iw, ih), Image.Resampling.LANCZOS)
                    if op < 100:
                        if resized.mode != 'RGBA':
                            resized = resized.convert('RGBA')
                        alpha = resized.split()[-1]
                        alpha = alpha.point(lambda a, o=op: int(a * o / 100.0))
                        resized.putalpha(alpha)
                    px, py = int(min(x1, x2)), int(min(y1, y2))
                    layer.paste(resized, (px, py), resized if resized.mode == 'RGBA' else None)
                except Exception:
                    pass
            elif obj['type'] == 'pen' and len(obj.get('points', [])) > 1:
                draw.line(obj['points'], fill=outline_rgba, width=w, joint="curve")

            result = Image.alpha_composite(result, layer)

        return result



    def _pil_to_b64(self, img):
        if img is None:
            return None
        buf = io.BytesIO()
        img.convert("RGBA").save(buf, format="PNG")
        return base64.b64encode(buf.getvalue()).decode("ascii")

    def _b64_to_pil(self, data):
        if not data:
            return None
        return Image.open(io.BytesIO(base64.b64decode(data))).convert("RGBA")

    def _serialize_objects(self):
        out = []
        for obj in self.objects:
            o = {k: v for k, v in obj.items() if k not in ("id", "pil_image", "_rz_cache")}
            if obj.get("type") in ("image", "fill_region") and obj.get("pil_image") is not None:
                o["pil_image_b64"] = self._pil_to_b64(obj["pil_image"])
            if "points" in o:
                o["points"] = [[float(p[0]), float(p[1])] for p in o["points"]]
            out.append(o)
        return out

    def _deserialize_objects(self, data):
        objs = []
        for o in data:
            obj = dict(o)
            b64 = obj.pop("pil_image_b64", None)
            if obj.get("type") in ("image", "fill_region") and b64:
                obj["pil_image"] = self._b64_to_pil(b64)
            if "points" in obj:
                obj["points"] = [(float(p[0]), float(p[1])) for p in obj["points"]]
            objs.append(obj)
        return objs

    def save_project(self, filepath=None, silent=False):
        """Düzenlenebilir proje (.pyint) — uzantı otomatik eklenir."""
        if not self.original_image:
            if not silent:
                messagebox.showwarning("Uyarı", "Kaydedilecek sayfa yok")
            return False
        if not filepath:
            initial = self.project_path or ""
            filepath = filedialog.asksaveasfilename(
                defaultextension=".pyint",
                initialfile=(initial.split("/")[-1] if initial else "proje.pyint"),
                filetypes=[("Proje (.pyint)", "*.pyint"), ("Tümü", "*.*")]
            )
        if not filepath:
            return False
        # Uzantıyı zorunlu ekle
        low = filepath.lower()
        if not low.endswith(".pyint"):
            filepath = filepath + ".pyint"
        try:
            payload = {
                "format": "ultimate-image-editor-project",
                "version": 1,
                "page": {
                    "width": self.original_image.width,
                    "height": self.original_image.height,
                    "image_b64": self._pil_to_b64(self.original_image),
                },
                "layers": copy.deepcopy(self.layers),
                "current_layer_id": self.current_layer_id,
                "layer_counter": self.layer_counter,
                "objects": self._serialize_objects(),
                "groups": {str(k): v for k, v in self.groups.items()},
                "group_counter": self.group_counter,
                "view": {
                    "scale": self.scale,
                    "pan_x": self.pan_x,
                    "pan_y": self.pan_y,
                    "initial_scale": getattr(self, "_initial_scale", self.scale),
                },
            }
            with open(filepath, "w", encoding="utf-8") as f:
                json.dump(payload, f, ensure_ascii=False)
            self.dirty = False
            self.project_path = filepath
            name = filepath.replace("\\", "/").split("/")[-1]
            if not silent:
                messagebox.showinfo("✅ Proje Kaydedildi", f"📁 {name}")
            self.status_label.config(text=f"💾 Proje kaydedildi: {name}", fg=self.colors["success"])
            return True
        except Exception as e:
            if not silent:
                messagebox.showerror("Hata", f"Proje kaydedilemedi:\n{e}")
            return False

    def open_project(self):
        """Proje aç — şekil/metin/resim düzenlenebilir kalır."""
        filepath = filedialog.askopenfilename(
            title="Proje Aç",
            filetypes=[("Proje (.pyint)", "*.pyint"), ("JSON", "*.json"), ("Tümü", "*.*")]
        )
        if not filepath:
            return
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                payload = json.load(f)
            page = payload.get("page") or {}
            img = self._b64_to_pil(page.get("image_b64"))
            if img is None:
                img = Image.new("RGBA", (int(page.get("width", 800)), int(page.get("height", 600))), (255, 255, 255, 255))

            self.history = []
            self.redo_stack = []
            self.original_image = img
            self.objects = self._deserialize_objects(payload.get("objects") or [])
            raw_g = payload.get("groups") or {}
            self.groups = {}
            for k, v in raw_g.items():
                try:
                    gid = int(k)
                except Exception:
                    gid = v.get("id", k)
                self.groups[gid] = v if isinstance(v, dict) else {"id": gid, "name": str(v)}
            self.group_counter = int(payload.get("group_counter") or (max(self.groups.keys()) + 1 if self.groups else 1))
            self.layers = payload.get("layers") or [{"id": 0, "name": "Katman 1", "visible": True}]
            self.current_layer_id = payload.get("current_layer_id", 0)
            self.layer_counter = payload.get("layer_counter", len(self.layers))
            self.selected_obj = None
            self.invalidate_cache()
            view = payload.get("view") or {}
            self.scale = float(view.get("scale") or 1.0)
            self._initial_scale = float(view.get("initial_scale") or self.scale)
            self.pan_x = float(view.get("pan_x") or 0)
            self.pan_y = float(view.get("pan_y") or 0)
            self.project_path = filepath
            self.dirty = False
            self.update_layer_ui()
            self.canvas.delete("all")
            self.redraw()
            self.status_label.config(text=f"📂 Proje açıldı: {filepath.split('/')[-1]}", fg=self.colors["success"])
        except Exception as e:
            messagebox.showerror("Hata", f"Proje açılamadı:\n{e}")

    def save_image(self):
        if not self.original_image:
            messagebox.showwarning("Uyarı", "Önce bir resim açın veya yeni sayfa oluşturun!")
            return
        
        filepath = filedialog.asksaveasfilename(
            title="Kaydet",
            defaultextension=".png",
            filetypes=[("PNG", "*.png"), ("JPEG", "*.jpg *.jpeg")],
        )
        if filepath:
            export_img = self.render_for_export()
            if filepath.lower().endswith(('.jpg', '.jpeg')):
                # JPEG için beyaz arkaplan
                bg = Image.new("RGBA", export_img.size, (255, 255, 255, 255))
                export_img = Image.alpha_composite(bg, export_img).convert("RGB")
            export_img.save(filepath)
            messagebox.showinfo("✅ Başarılı", f"Resim kaydedildi!\n📁 {filepath.split('/')[-1]}")


    def on_closing(self):
        """Kapatırken kaydedilmemiş değişiklik varsa sor."""
        if not getattr(self, "dirty", False):
            self.root.destroy()
            return

        # Özel dialog: Proje kaydet / Kaydetme / İptal
        dlg = tk.Toplevel(self.root)
        dlg.title("Kaydet")
        dlg.configure(bg=self.colors["bg_medium"])
        dlg.resizable(False, False)
        dlg.transient(self.root)
        dlg.grab_set()

        tk.Label(
            dlg,
            text="Kaydedilmemiş değişiklikler var.\nKapatmadan önce proje kaydedilsin mi?",
            bg=self.colors["bg_medium"],
            fg=self.colors["text"],
            font=("Segoe UI", 11),
            justify="center",
        ).pack(padx=24, pady=(20, 12))

        result = {"action": "cancel"}

        def do_save():
            result["action"] = "save"
            dlg.destroy()

        def do_discard():
            result["action"] = "discard"
            dlg.destroy()

        def do_cancel():
            result["action"] = "cancel"
            dlg.destroy()

        row = tk.Frame(dlg, bg=self.colors["bg_medium"])
        row.pack(pady=(8, 20))
        tk.Button(row, text="💾 Kaydet", command=do_save, bg=self.colors["accent"], fg="white",
                  relief="flat", font=("Segoe UI", 10, "bold"), padx=14, pady=6, cursor="hand2").pack(side=tk.LEFT, padx=6)
        tk.Button(row, text="Kaydetme", command=do_discard, bg=self.colors["bg_light"], fg=self.colors["text"],
                  relief="flat", font=("Segoe UI", 10), padx=14, pady=6, cursor="hand2").pack(side=tk.LEFT, padx=6)
        tk.Button(row, text="İptal", command=do_cancel, bg=self.colors["bg_light"], fg=self.colors["text"],
                  relief="flat", font=("Segoe UI", 10), padx=14, pady=6, cursor="hand2").pack(side=tk.LEFT, padx=6)

        dlg.update_idletasks()
        x = self.root.winfo_rootx() + (self.root.winfo_width() - dlg.winfo_width()) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - dlg.winfo_height()) // 2
        dlg.geometry(f"+{x}+{y}")
        self.root.wait_window(dlg)

        if result["action"] == "cancel":
            return
        if result["action"] == "save":
            # Varsa mevcut proje yoluna, yoksa dialog
            ok = self.save_project(filepath=self.project_path if self.project_path else None)
            if not ok:
                return  # kaydetmedi / iptal — kapatma
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    
    try:
        root.iconbitmap(resource_path("pyint.ico"))
    except Exception as e:
        print(f"Icon could not be loaded: {e}")
        
    app = UltimateImageEditor(root)
    root.mainloop()
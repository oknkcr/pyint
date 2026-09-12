# PYINT

A modern and comprehensive **Python / Tkinter-based image editing application**.

PYINT Pro combines image editing, drawing, shapes, text, layers, groups, cropping, screenshot capture, zooming, color picking, transformations, and editable project saving in a single desktop application.

## Features

### File and Project Management
- Open PNG, JPG, and JPEG images
- Create a new blank page
- Add images as editable objects
- Save the final image as PNG or JPEG
- Save editable projects in `.pyint` format
- Open `.pyint` and supported JSON projects

### Drawing Tools
- Select / Move
- Freehand Brush
- Rectangle
- Square
- Circle
- Hexagon
- Star
- Callout
- Triangle
- Curve
- Arrow
- Waypoint-based Arrow Path
- Text

### Editing Tools
- Color picker
- Eyedropper
- Bucket fill
- Crop
- Region zoom
- Page resizing
- Object movement and multi-selection
- Copy and paste
- Copy and paste styles
- Lock and unlock objects
- Undo and redo

### Layers and Groups
- Create new layers
- Rename layers
- Show or hide layers
- Change object stacking order
- Bring objects to front or send them to back
- Group multiple objects
- Ungroup objects
- Rename groups

### Transformations
- Rotate by 15 degrees
- Rotate by 90 degrees
- Horizontal mirror
- Vertical mirror
- Precise movement with keyboard arrow keys

### View and Interface
- Fit image to workspace
- 1:1 original size view
- Mouse wheel zoom
- Right-click pan
- Light and dark themes
- Active tool indicator
- Tooltips
- Keyboard shortcuts

### Screenshot Capture
- Capture a selected screen region
- Drag to select an area
- Edge and snap assistance
- Edit the selected capture region

---

## Requirements

- Python 3.10 or newer is recommended
- Pillow

Install the required dependency:

```bash
pip install pillow
```

---

## Running the Application

Run the Python file directly:

```bash
python pyint.py
```
---

## Supported File Formats

| Operation | Formats |
|---|---|
| Open Image | PNG, JPG, JPEG |
| Save Image | PNG, JPG, JPEG |
| Save Project | PYINT |
| Open Project | PYINT, JSON |

> The `.pyint` project format stores editable project information such as objects, layers, groups, page data, and view settings.

---

## Keyboard Shortcuts

### File Operations

| Shortcut | Action |
|---|---|
| Ctrl+O | Open Image |
| Ctrl+Shift+O | Open Project |
| Ctrl+S | Save Image |
| Ctrl+Shift+S | Save Project |
| Ctrl+N | New Page |
| Ctrl+I | Add Image |
| F9 | Screenshot Capture |

### Editing

| Shortcut | Action |
|---|---|
| Ctrl+Z | Undo |
| Ctrl+Y | Redo |
| Ctrl+C / Ctrl+V | Copy / Paste |
| Delete / Backspace | Delete Selected Object |
| Ctrl+A | Select All |
| Ctrl+G | Group Selected Objects |
| Ctrl+Shift+G | Ungroup |
| Ctrl+L | Lock / Unlock Selected Object |
| Ctrl+Shift+L | Unlock All |
| F2 | Edit Selected Text |
| Arrow Keys | Move Selected Object |

### Tools

| Shortcut | Tool |
|---|---|
| V / H | Select / Move |
| B | Brush |
| R | Rectangle |
| U | Square |
| O | Circle |
| T | Triangle |
| P | Hexagon |
| W | Star |
| L / M | Callout |
| C | Curve |
| A | Arrow |
| Q | Arrow Path |
| X | Text |
| G / F | Fill |
| I | Eyedropper |
| K | Crop |
| Z | Region Zoom |

### View and Transform

| Shortcut | Action |
|---|---|
| Ctrl+0 | Fit to Workspace |
| Ctrl+1 | 1:1 Original Size |
| Ctrl++ | Zoom In |
| Ctrl+- | Zoom Out |
| Ctrl+T | Toggle Theme |
| F1 | Keyboard Shortcuts |
| [ / ] | Rotate 15° |
| Ctrl+[ / Ctrl+] | Rotate 90° |
| Ctrl+R | Rotate 90° Right |
| Ctrl+Shift+R | Rotate 90° Left |
| Ctrl+H | Horizontal Mirror |
| Ctrl+J | Vertical Mirror |

### Style

| Shortcut | Action |
|---|---|
| Ctrl+Shift+C | Copy Style |
| Ctrl+Shift+V | Paste Style |

---

## Quick Start

1. Click **Open Image** to load a PNG, JPG, or JPEG image.
2. Adjust the crop area if necessary.
3. Select a drawing or editing tool from the toolbar.
4. Configure the line color, fill color, thickness, font size, and opacity.
5. Create and edit objects on the canvas.
6. Use the Layers and Groups panels to organize your work.
7. Save the editable project using **Save Project**.
8. Export the final result using **Save Image**.

---

## Project Structure

The application is built around the following main components:

- `UltimateImageEditor` main application class
- Tkinter-based user interface
- Pillow-based image processing and export
- Object-based drawing system
- Layer management system
- Group management system
- Undo / Redo history
- JSON-based `.pyint` project format
- High-quality rendering and export system

---

## License

The application includes MIT License information.

**Developer:** Okan KOÇER

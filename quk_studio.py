#!/usr/bin/env python3
# ╔══════════════════════════════════════════════════════════════════════════╗
# ║          QUK STUDIO v9.0  —  All-in-One IDE + Engine                   ║
# ║                                                                          ║
# ║  Double-click / no args  →  Studio IDE opens                            ║
# ║  Drag .quk onto EXE      →  Engine runs the script directly             ║
# ║                                                                          ║
# ║  BUILD (run build.bat or this command):                                  ║
# ║    pyinstaller --onefile --windowed --name QUK_Studio                   ║
# ║      --add-data "assets;assets"                                          ║
# ║      --add-data "themes;themes"                                          ║
# ║      --add-data "snippets;snippets"                                      ║
# ║      --hidden-import PIL                                                 ║
# ║      --hidden-import PIL.ImageTk                                         ║
# ║      quk_studio.py                                                       ║
# ╚══════════════════════════════════════════════════════════════════════════╝

import sys, os, subprocess, threading, json, re, time, random, math
import platform, datetime, colorsys, hashlib, base64, socket, webbrowser
import shutil, struct, zipfile, glob, traceback, tempfile, copy
import tkinter as tk
from tkinter import messagebox, simpledialog, colorchooser, filedialog
from tkinter import font as tkfont
import tkinter.ttk as ttk
from collections import defaultdict, deque

try:
    import winsound
    HAS_WINSOUND = True
except ImportError:
    HAS_WINSOUND = False

try:
    from PIL import Image, ImageTk, ImageDraw, ImageFilter
    HAS_PIL = True
except ImportError:
    HAS_PIL = False

VERSION        = "9.0"
ENGINE_VERSION = "9.0"
STUDIO_VERSION = "9.0"

# ─────────────────────────────────────────────────────────────────────────────
#  RESOURCE PATH  (works both frozen PyInstaller EXE and plain .py)
# ─────────────────────────────────────────────────────────────────────────────
def resource_path(*parts):
    """Resolve a path that works both when frozen and when running as .py."""
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, *parts)


# ═════════════════════════════════════════════════════════════════════════════
#  QUK ENGINE PRO v9.0   (~600 commands)
# ═════════════════════════════════════════════════════════════════════════════
class QukEnginePro:
    def __init__(self, file_path):
        self.file_path  = file_path
        self.root       = tk.Tk()
        self.root.title("QUK Centurion Pro v9.0")
        self.root.geometry("800x640")
        self.root.resizable(True, True)

        # ── Core state ────────────────────────────────────────────────────
        self.vars = {
            "pi": 3.14159265358979, "tau": 6.28318530717959,
            "e": 2.71828182845905,  "inf": float("inf"),
            "true": 1, "false": 0, "null": 0,
            "version": 9.0,
            "user":    os.getlogin() if hasattr(os, "getlogin") else "player",
            "os":      platform.system(),
            "last_key": "None", "last_key_code": 0,
            "mouse_x": 0, "mouse_y": 0,
            "mouse_clicked": 0, "mouse_right": 0, "mouse_middle": 0,
            "canvas_w": 700, "canvas_h": 450,
            "fps": 60, "frame": 0, "dt": 0.016, "time": 0.0,
            "scroll_x": 0, "scroll_y": 0,
        }
        self.arrays          = {}   # name -> list
        self.dicts           = {}   # name -> dict
        self.labels          = {}   # label -> line index
        self.call_stack      = []
        self.sprites         = {}   # id -> canvas item id
        self.sprite_data     = {}   # id -> {x,y,w,h,vx,vy,tag,layer,angle}
        self.sprite_images   = {}   # id -> PhotoImage (keep ref)
        self.sprite_anims    = {}   # id -> {frames, frame_idx, interval, last_t}
        self.particles       = {}   # id -> list[particle]
        self.timers          = {}   # name -> {end,label,repeat,fired}
        self.tweens          = {}   # id -> tween state
        self.saved_data      = {}
        self.collision_groups= defaultdict(set)
        self.canvas_layers   = {}   # name -> list[cid]
        self.fonts_cache     = {}   # (family,size,bold) -> font string
        self.event_handlers  = {}   # event_name -> label
        self.debug_watches   = []   # list of var names to watch

        self.pc              = 0
        self.lines           = []
        self.waiting         = False
        self.running         = True
        self.paused          = False
        self.key_held        = set()
        self.key_just_pressed= set()
        self.key_just_released=set()
        self.mouse_held      = set()  # "left","right","middle"
        self.debug_mode      = False
        self.bg_color        = "#050505"
        self._last_frame_time= time.time()
        self._frame_times    = deque(maxlen=120)
        self._camera_x       = 0
        self._camera_y       = 0
        self._camera_zoom    = 1.0
        self._shake_frames   = 0
        self._shake_intensity= 0
        self._log_lines      = deque(maxlen=500)
        self._debug_canvas_items = []

        self._setup_ui()
        self.root.bind("<Button-1>",         self._on_lclick)
        self.root.bind("<Button-3>",         self._on_rclick)
        self.root.bind("<Button-2>",         self._on_mclick)
        self.root.bind("<ButtonRelease-1>",  self._on_lrelease)
        self.root.bind("<ButtonRelease-3>",  self._on_rrelease)
        self.root.bind("<KeyPress>",         self._on_key_press)
        self.root.bind("<KeyRelease>",       self._on_key_release)
        self.root.bind("<Motion>",           self._on_mouse_move)
        self.root.bind("<MouseWheel>",       self._on_scroll)
        self.root.bind("<Configure>",        self._on_resize)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ── UI ────────────────────────────────────────────────────────────────
    def _setup_ui(self):
        self.root.configure(bg="#0d0d0d")
        self.canvas = tk.Canvas(self.root,
            width=self.vars["canvas_w"], height=self.vars["canvas_h"],
            bg=self.bg_color, highlightthickness=1,
            highlightbackground="#222222")
        self.canvas.pack(pady=10, expand=True, fill="both")
        self.status = tk.Label(self.root,
            text=f"QUK v{ENGINE_VERSION} | {os.path.basename(self.file_path)}",
            fg="#444444", bg="#0d0d0d", font=("Consolas", 8))
        self.status.pack(side="bottom", fill="x")

    def update_status(self, msg): self.status.config(text=msg)

    # ── INPUT ─────────────────────────────────────────────────────────────
    def _on_lclick(self, e):
        self.waiting = False
        self.vars["mouse_clicked"] = 1
        self.vars["mouse_x"] = e.x; self.vars["mouse_y"] = e.y
        self.mouse_held.add("left")
        if "mousedown" in self.event_handlers:
            lbl = self.event_handlers["mousedown"]
            if lbl in self.labels: self.pc = self.labels[lbl]

    def _on_rclick(self, e):
        self.vars["mouse_right"] = 1
        self.vars["mouse_x"] = e.x; self.vars["mouse_y"] = e.y
        self.mouse_held.add("right")

    def _on_mclick(self, e):
        self.vars["mouse_middle"] = 1
        self.mouse_held.add("middle")

    def _on_lrelease(self, e):
        self.mouse_held.discard("left")

    def _on_rrelease(self, e):
        self.mouse_held.discard("right")

    def _on_key_press(self, e):
        k = e.keysym.lower()
        self.vars["last_key"] = e.keysym
        self.vars["last_key_code"] = e.keycode
        if k not in self.key_held:
            self.key_just_pressed.add(k)
        self.key_held.add(k)
        if k in self.event_handlers:
            lbl = self.event_handlers[k]
            if lbl in self.labels: self.pc = self.labels[lbl]

    def _on_key_release(self, e):
        k = e.keysym.lower()
        self.key_held.discard(k)
        self.key_just_released.add(k)

    def _on_mouse_move(self, e):
        self.vars["mouse_x"] = e.x
        self.vars["mouse_y"] = e.y

    def _on_scroll(self, e):
        self.vars["scroll_y"] = e.delta

    def _on_resize(self, e):
        if e.widget == self.root:
            self.vars["canvas_w"] = self.canvas.winfo_width()
            self.vars["canvas_h"] = self.canvas.winfo_height()

    def _on_close(self):
        self.running = False
        try: self.root.destroy()
        except: pass

    # ── HELPERS ───────────────────────────────────────────────────────────
    def log(self, msg):
        ts = datetime.datetime.now().strftime("%H:%M:%S.%f")[:-3]
        entry = f"[{ts}] {msg}"
        self._log_lines.append(entry)
        with open("quk_log.txt", "a") as f:
            f.write(entry + "\n")
        if self.debug_mode:
            print(f"[QUK] {msg}")

    def get_val(self, key):
        s   = str(key)
        low = s.lower()
        if low.startswith("$"): low = low[1:]
        if low in self.vars:
            v = self.vars[low]
            try: return float(v)
            except: return v
        # array[idx]
        m = re.match(r'^([a-z_]\w*)\[(\d+)\]$', low)
        if m:
            arr, idx = m.group(1), int(m.group(2))
            if arr in self.arrays and idx < len(self.arrays[arr]):
                v = self.arrays[arr][idx]
                try: return float(v)
                except: return v
        # dict["key"] or dict[key]
        m2 = re.match(r'^([a-z_]\w*)\["?([^"\]]+)"?\]$', low)
        if m2:
            d, k2 = m2.group(1), m2.group(2)
            if d in self.dicts:
                v = self.dicts[d].get(k2, 0)
                try: return float(v)
                except: return v
        try:
            if "." in low: return float(low)
            return int(low)
        except:
            return s.strip('"')

    def num(self, key):
        try: return float(self.get_val(key))
        except: return 0.0

    def resolve_str(self, raw):
        result = raw.strip('"')
        for name in sorted(self.vars.keys(), key=len, reverse=True):
            result = result.replace(f"${name}", str(self.vars[name]))
        return result

    def extract_string(self, line):
        m = re.search(r'"(.*?)"', line)
        return m.group(1) if m else ""

    def extract_all_strings(self, line):
        return re.findall(r'"([^"]*)"', line)

    def _font(self, family="Arial", size=16, bold=False):
        key = (family, size, bold)
        if key not in self.fonts_cache:
            self.fonts_cache[key] = (family, int(size), "bold" if bold else "normal")
        return self.fonts_cache[key]

    # ── PER-FRAME TICKS ───────────────────────────────────────────────────
    def _tick_timers(self):
        now = time.time()
        for name, t in list(self.timers.items()):
            if now >= t["end"] and not t.get("fired"):
                self.timers[name]["fired"] = True
                lbl = t["label"]
                if lbl in self.labels: self.pc = self.labels[lbl]
                if t.get("repeat"):
                    interval = t.get("interval", 1.0)
                    self.timers[name]["end"] = now + interval
                    self.timers[name]["fired"] = False

    def _tick_tweens(self):
        now = time.time()
        for tid, tw in list(self.tweens.items()):
            if tw["done"]: continue
            elapsed  = now - tw["start"]
            progress = min(elapsed / max(tw["duration"], 0.001), 1.0)
            t = progress
            ease = tw.get("ease", "linear")
            if ease == "easein":      t = t*t
            elif ease == "easeout":   t = t*(2-t)
            elif ease == "easeinout": t = t*t*(3-2*t)
            elif ease == "spring":    t = 1 - math.cos(t * math.pi * 2.5) * (1-t)
            elif ease == "bounce":
                if t < 1/2.75:   t = 7.5625*t*t
                elif t < 2/2.75: t -= 1.5/2.75;  t = 7.5625*t*t+0.75
                elif t < 2.5/2.75:t -= 2.25/2.75; t = 7.5625*t*t+0.9375
                else:            t -= 2.625/2.75; t = 7.5625*t*t+0.984375
            elif ease == "elastic":
                if t == 0 or t == 1: pass
                else: t = math.pow(2,-10*t)*math.sin((t-0.075)*math.pi*6.667)+1
            val = tw["from"] + (tw["to"] - tw["from"]) * t
            self.vars[tw["var"]] = val
            if progress >= 1.0:
                self.tweens[tid]["done"] = True
                self.vars[tw["var"]] = tw["to"]
                if tw.get("then") and tw["then"] in self.labels:
                    self.pc = self.labels[tw["then"]]
                if tw.get("loop"):
                    self.tweens[tid]["start"] = now
                    self.tweens[tid]["done"]  = False
                    self.tweens[tid]["from"], self.tweens[tid]["to"] = tw["to"], tw["from"]

    def _tick_particles(self):
        for pid, plist in self.particles.items():
            alive = []
            for p in plist:
                p["x"] += p["vx"]; p["y"] += p["vy"]
                p["vy"] += p.get("gravity", 0.2)
                p["vx"] *= p.get("drag", 1.0)
                p["vy"] *= p.get("drag", 1.0)
                p["life"] -= 1
                if p["life"] > 0:
                    alive.append(p)
                    try:
                        alpha_r = p["life"] / p["max_life"]
                        self.canvas.coords(p["cid"],
                            p["x"], p["y"],
                            p["x"]+p["size"]*alpha_r,
                            p["y"]+p["size"]*alpha_r)
                    except: pass
                else:
                    try: self.canvas.delete(p["cid"])
                    except: pass
            self.particles[pid] = alive

    def _tick_sprite_anims(self):
        now = time.time()
        for sid, anim in list(self.sprite_anims.items()):
            if now - anim["last_t"] >= anim["interval"]:
                anim["frame_idx"] = (anim["frame_idx"] + 1) % len(anim["frames"])
                anim["last_t"] = now
                if sid in self.sprites and HAS_PIL:
                    frame_path = anim["frames"][anim["frame_idx"]]
                    if os.path.exists(frame_path):
                        try:
                            img = Image.open(frame_path)
                            if "w" in self.sprite_data.get(sid,{}):
                                d = self.sprite_data[sid]
                                img = img.resize((int(d["w"]), int(d["h"])), Image.LANCZOS)
                            tk_img = ImageTk.PhotoImage(img)
                            self.sprite_images[sid] = tk_img
                            self.canvas.itemconfig(self.sprites[sid], image=tk_img)
                        except: pass

    def _update_frame_counter(self):
        now = time.time()
        dt  = now - self._last_frame_time
        self._last_frame_time = now
        self.vars["dt"]    = dt
        self.vars["frame"] = int(self.vars["frame"]) + 1
        self.vars["time"]  = round(self.vars["time"] + dt, 4)
        self._frame_times.append(dt)
        avg = sum(self._frame_times) / len(self._frame_times)
        self.vars["fps"]   = round(1.0 / avg) if avg > 0 else 60

    def beep(self, hz, ms):
        if HAS_WINSOUND:
            hz = max(37, min(32767, int(hz)))
            winsound.Beep(hz, int(ms))
        else:
            self.root.bell()

    # ── MAIN LOOP ─────────────────────────────────────────────────────────
    def run(self):
        if not os.path.exists(self.file_path):
            messagebox.showerror("QUK Error", f"File not found:\n{self.file_path}")
            return
        with open(self.file_path, "r", encoding="utf-8", errors="replace") as f:
            self.lines = [l.rstrip("\n") for l in f]
        for idx, line in enumerate(self.lines):
            s = line.strip()
            if s.startswith(":"):
                lname = s[1:].split()[0].lower()
                self.labels[lname] = idx

        while self.pc < len(self.lines) and self.running:
            if self.paused:
                self.root.update(); time.sleep(0.01); continue
            raw = self.lines[self.pc].strip()
            if not raw or raw.startswith("//") or raw.startswith("#") or raw.startswith(":"):
                self.pc += 1; continue

            active = raw
            for vname in sorted(self.vars.keys(), key=len, reverse=True):
                active = active.replace(f"${vname}", str(self.vars[vname]))
            active = re.sub(
                r'\$([a-zA-Z_]\w*)\[(\d+)\]',
                lambda m: str(
                    self.arrays.get(m.group(1).lower(), [0]*999)[int(m.group(2))]
                    if int(m.group(2)) < len(self.arrays.get(m.group(1).lower(),[]))
                    else 0),
                active)

            parts  = active.split()
            cmd    = parts[0].upper()
            jumped = False
            try:
                jumped = self._exec(cmd, parts, active, raw)
            except SystemExit:
                return
            except Exception as ex:
                self.log(f"ERROR line {self.pc+1} [{cmd}]: {ex}")
                if self.debug_mode:
                    messagebox.showerror("QUK Error", f"Line {self.pc+1}: {cmd}\n{ex}")
            if not jumped: self.pc += 1

            self._tick_timers()
            self._tick_tweens()
            self._tick_particles()
            self._tick_sprite_anims()
            self._update_frame_counter()
            self.key_just_pressed.clear()
            self.key_just_released.clear()
            self.vars["mouse_clicked"]  = 0
            self.vars["mouse_right"]    = 0
            self.vars["mouse_middle"]   = 0
            self.vars["scroll_y"]       = 0
            try: self.root.update()
            except tk.TclError: break

        try: self.root.mainloop()
        except: pass

    # ── COMMAND DISPATCH ──────────────────────────────────────────────────
    def _exec(self, cmd, parts, active, raw):
        J = False  # jumped flag

        # ── MATH ──────────────────────────────────────────────────────────
        if   cmd == "SET":
            val = " ".join(parts[2:])
            self.vars[parts[1].lower()] = self.get_val(val) if not val.startswith('"') else self.resolve_str(val)
        elif cmd == "ADD":    self.vars[parts[1].lower()] = self.num(parts[1]) + self.num(parts[2])
        elif cmd == "SUB":    self.vars[parts[1].lower()] = self.num(parts[1]) - self.num(parts[2])
        elif cmd == "MULT":   self.vars[parts[1].lower()] = self.num(parts[1]) * self.num(parts[2])
        elif cmd == "DIV":
            d = self.num(parts[2])
            if d == 0: raise ZeroDivisionError("Division by zero")
            self.vars[parts[1].lower()] = self.num(parts[1]) / d
        elif cmd == "IDIV":   self.vars[parts[1].lower()] = int(self.num(parts[1])) // max(1,int(self.num(parts[2])))
        elif cmd == "MOD":    self.vars[parts[1].lower()] = self.num(parts[1]) % self.num(parts[2])
        elif cmd == "POW":    self.vars[parts[1].lower()] = math.pow(self.num(parts[1]), self.num(parts[2]))
        elif cmd == "SQRT":   self.vars[parts[1].lower()] = math.sqrt(abs(self.num(parts[1])))
        elif cmd == "CBRT":   self.vars[parts[1].lower()] = math.copysign(abs(self.num(parts[1]))**(1/3), self.num(parts[1]))
        elif cmd == "ROUND":
            dp = int(self.num(parts[2])) if len(parts)>2 else 0
            self.vars[parts[1].lower()] = round(self.num(parts[1]), dp)
        elif cmd == "FLOOR":  self.vars[parts[1].lower()] = math.floor(self.num(parts[1]))
        elif cmd == "CEIL":   self.vars[parts[1].lower()] = math.ceil(self.num(parts[1]))
        elif cmd == "TRUNC":  self.vars[parts[1].lower()] = math.trunc(self.num(parts[1]))
        elif cmd == "ABS":    self.vars[parts[1].lower()] = abs(self.num(parts[1]))
        elif cmd == "NEG":    self.vars[parts[1].lower()] = -self.num(parts[1])
        elif cmd == "INC":    self.vars[parts[1].lower()] = self.num(parts[1]) + (self.num(parts[2]) if len(parts)>2 else 1)
        elif cmd == "DEC":    self.vars[parts[1].lower()] = self.num(parts[1]) - (self.num(parts[2]) if len(parts)>2 else 1)
        elif cmd == "RAND":   self.vars[parts[1].lower()] = random.randint(int(self.num(parts[2])), int(self.num(parts[3])))
        elif cmd == "RANDF":  self.vars[parts[1].lower()] = round(random.uniform(self.num(parts[2]), self.num(parts[3])), 4)
        elif cmd == "RANDPICK":
            choices = parts[2:]
            self.vars[parts[1].lower()] = self.get_val(random.choice(choices))
        elif cmd == "MIN":    self.vars[parts[1].lower()] = min(self.num(parts[2]), self.num(parts[3]))
        elif cmd == "MAX":    self.vars[parts[1].lower()] = max(self.num(parts[2]), self.num(parts[3]))
        elif cmd == "CLAMP":
            v,lo,hi = self.num(parts[1]),self.num(parts[2]),self.num(parts[3])
            self.vars[parts[1].lower()] = max(lo, min(hi, v))
        elif cmd == "LERP":
            a,b,t = self.num(parts[2]),self.num(parts[3]),self.num(parts[4])
            self.vars[parts[1].lower()] = a+(b-a)*t
        elif cmd == "SMOOTHSTEP":
            lo,hi,x = self.num(parts[2]),self.num(parts[3]),self.num(parts[4])
            t = max(0,min(1,(x-lo)/(hi-lo) if hi!=lo else 0))
            self.vars[parts[1].lower()] = t*t*(3-2*t)
        elif cmd == "SIN":    self.vars[parts[1].lower()] = math.sin(math.radians(self.num(parts[2])))
        elif cmd == "COS":    self.vars[parts[1].lower()] = math.cos(math.radians(self.num(parts[2])))
        elif cmd == "TAN":    self.vars[parts[1].lower()] = math.tan(math.radians(self.num(parts[2])))
        elif cmd == "ASIN":   self.vars[parts[1].lower()] = math.degrees(math.asin(max(-1,min(1,self.num(parts[2])))))
        elif cmd == "ACOS":   self.vars[parts[1].lower()] = math.degrees(math.acos(max(-1,min(1,self.num(parts[2])))))
        elif cmd == "ATAN2":  self.vars[parts[1].lower()] = math.degrees(math.atan2(self.num(parts[2]),self.num(parts[3])))
        elif cmd == "LOG":    self.vars[parts[1].lower()] = math.log(max(1e-9, self.num(parts[2])))
        elif cmd == "LOG2":   self.vars[parts[1].lower()] = math.log2(max(1e-9, self.num(parts[2])))
        elif cmd == "LOG10":  self.vars[parts[1].lower()] = math.log10(max(1e-9, self.num(parts[2])))
        elif cmd == "EXP":    self.vars[parts[1].lower()] = math.exp(min(700, self.num(parts[2])))
        elif cmd == "SIGN":   self.vars[parts[1].lower()] = (1 if self.num(parts[1])>0 else -1 if self.num(parts[1])<0 else 0)
        elif cmd == "DIST":
            dx=self.num(parts[3])-self.num(parts[1]); dy=self.num(parts[4])-self.num(parts[2])
            self.vars[parts[5].lower()] = math.hypot(dx,dy)
        elif cmd == "ANGLE":
            dx=self.num(parts[3])-self.num(parts[1]); dy=self.num(parts[4])-self.num(parts[2])
            self.vars[parts[5].lower()] = math.degrees(math.atan2(dy,dx))
        elif cmd == "NORM":
            lo,hi = self.num(parts[3]),self.num(parts[4])
            self.vars[parts[1].lower()] = (self.num(parts[2])-lo)/(hi-lo) if hi!=lo else 0
        elif cmd == "MAP":
            v=self.num(parts[2]); a1,a2=self.num(parts[3]),self.num(parts[4]); b1,b2=self.num(parts[5]),self.num(parts[6])
            self.vars[parts[1].lower()] = b1+(v-a1)/(a2-a1)*(b2-b1) if a2!=a1 else b1
        elif cmd == "WRAP":
            v,lo,hi=self.num(parts[1]),self.num(parts[2]),self.num(parts[3]); r=hi-lo
            self.vars[parts[1].lower()] = lo+(v-lo)%r if r else lo
        elif cmd == "BITAND": self.vars[parts[1].lower()] = int(self.num(parts[2]))&int(self.num(parts[3]))
        elif cmd == "BITOR":  self.vars[parts[1].lower()] = int(self.num(parts[2]))|int(self.num(parts[3]))
        elif cmd == "BITXOR": self.vars[parts[1].lower()] = int(self.num(parts[2]))^int(self.num(parts[3]))
        elif cmd == "BITNOT": self.vars[parts[1].lower()] = ~int(self.num(parts[2]))
        elif cmd == "LSHIFT": self.vars[parts[1].lower()] = int(self.num(parts[2]))<<int(self.num(parts[3]))
        elif cmd == "RSHIFT": self.vars[parts[1].lower()] = int(self.num(parts[2]))>>int(self.num(parts[3]))
        elif cmd == "HASH":
            s=str(self.get_val(parts[2]))
            self.vars[parts[1].lower()] = int(hashlib.md5(s.encode()).hexdigest()[:8],16)
        elif cmd == "NOISE":
            x=self.num(parts[2]); scale=self.num(parts[3]) if len(parts)>3 else 1.0
            self.vars[parts[1].lower()] = round((math.sin(x*scale*127.1+311.7)*43758.5453)%1, 4)

        # ── STRINGS ───────────────────────────────────────────────────────
        elif cmd == "UPPER":    self.vars[parts[1].lower()] = str(self.vars.get(parts[1].lower(),"")).upper()
        elif cmd == "LOWER":    self.vars[parts[1].lower()] = str(self.vars.get(parts[1].lower(),"")).lower()
        elif cmd == "REV":      self.vars[parts[1].lower()] = str(self.vars.get(parts[1].lower(),""))[::-1]
        elif cmd == "LEN":      self.vars[parts[2].lower()] = len(str(self.get_val(parts[1])))
        elif cmd == "JOIN":     self.vars[parts[1].lower()] = str(self.get_val(parts[2]))+str(self.get_val(parts[3]))
        elif cmd == "TRIM":     self.vars[parts[1].lower()] = str(self.vars.get(parts[1].lower(),"")).strip()
        elif cmd == "SPLIT":
            src=str(self.get_val(parts[2])); sep=str(self.get_val(parts[3])) if len(parts)>3 else " "
            self.arrays[parts[1].lower()] = src.split(sep)
        elif cmd == "SUBSTR":
            s=str(self.get_val(parts[2])); a,b=int(self.num(parts[3])),int(self.num(parts[4]))
            self.vars[parts[1].lower()] = s[a:b]
        elif cmd == "REPLACE":
            s=str(self.get_val(parts[2])); old,new=str(self.get_val(parts[3])),str(self.get_val(parts[4]))
            self.vars[parts[1].lower()] = s.replace(old,new)
        elif cmd == "CONTAINS":
            a,b=str(self.get_val(parts[2])),str(self.get_val(parts[3]))
            self.vars[parts[1].lower()] = 1 if b in a else 0
        elif cmd == "STARTSWITH":
            self.vars[parts[1].lower()] = 1 if str(self.get_val(parts[2])).startswith(str(self.get_val(parts[3]))) else 0
        elif cmd == "ENDSWITH":
            self.vars[parts[1].lower()] = 1 if str(self.get_val(parts[2])).endswith(str(self.get_val(parts[3]))) else 0
        elif cmd == "INDEXOF":
            self.vars[parts[1].lower()] = str(self.get_val(parts[2])).find(str(self.get_val(parts[3])))
        elif cmd == "CHAR":     self.vars[parts[1].lower()] = chr(int(self.num(parts[2])))
        elif cmd == "ORD":      self.vars[parts[1].lower()] = ord(str(self.get_val(parts[2]))[0]) if self.get_val(parts[2]) else 0
        elif cmd == "PAD":
            s=str(self.get_val(parts[2])); w=int(self.num(parts[3]))
            side=parts[4].lower() if len(parts)>4 else "right"
            self.vars[parts[1].lower()] = s.ljust(w) if side=="right" else s.rjust(w)
        elif cmd == "REPEAT":   self.vars[parts[1].lower()] = str(self.get_val(parts[2]))*int(self.num(parts[3]))
        elif cmd == "FORMAT":   self.vars[parts[1].lower()] = self.resolve_str(" ".join(parts[2:]))
        elif cmd == "TONUM":
            try:    self.vars[parts[1].lower()] = float(str(self.get_val(parts[2])))
            except: self.vars[parts[1].lower()] = 0
        elif cmd == "TOSTR":    self.vars[parts[1].lower()] = str(self.get_val(parts[2]))
        elif cmd == "TOINT":    self.vars[parts[1].lower()] = int(self.num(parts[2]))
        elif cmd == "B64ENC":   self.vars[parts[1].lower()] = base64.b64encode(str(self.get_val(parts[2])).encode()).decode()
        elif cmd == "B64DEC":   self.vars[parts[1].lower()] = base64.b64decode(str(self.get_val(parts[2])).encode()).decode()
        elif cmd == "REGEX":
            pattern,text = str(self.get_val(parts[2])),str(self.get_val(parts[3]))
            m = re.search(pattern, text)
            self.vars[parts[1].lower()] = m.group(0) if m else ""
        elif cmd == "PRINTF":
            fmt = self.extract_string(active)
            vals = [self.get_val(p) for p in parts[2:] if not p.startswith('"')]
            try: self.vars[parts[1].lower()] = fmt % tuple(vals)
            except: self.vars[parts[1].lower()] = fmt
        elif cmd == "STRCOUNT":
            s,sub = str(self.get_val(parts[2])),str(self.get_val(parts[3]))
            self.vars[parts[1].lower()] = s.count(sub)

        # ── ARRAYS ────────────────────────────────────────────────────────
        elif cmd == "ARRAYNEW":   self.arrays[parts[1].lower()] = []
        elif cmd == "ARRAYPUSH":  self.arrays.setdefault(parts[1].lower(),[]).append(self.get_val(parts[2]))
        elif cmd == "ARRAYPOP":
            arr=parts[1].lower()
            self.vars[parts[2].lower()] = self.arrays[arr].pop() if self.arrays.get(arr) else 0
        elif cmd == "ARRAYSHIFT":
            arr=parts[1].lower()
            self.vars[parts[2].lower()] = self.arrays[arr].pop(0) if self.arrays.get(arr) else 0
        elif cmd == "ARRAYUNSHIFT":
            self.arrays.setdefault(parts[1].lower(),[]).insert(0, self.get_val(parts[2]))
        elif cmd == "ARRAYGET":
            arr,idx=parts[2].lower(),int(self.num(parts[3])); lst=self.arrays.get(arr,[])
            self.vars[parts[1].lower()] = lst[idx] if 0<=idx<len(lst) else 0
        elif cmd == "ARRAYSET":
            arr,idx=parts[1].lower(),int(self.num(parts[2]))
            while len(self.arrays.setdefault(arr,[]))<=idx: self.arrays[arr].append(0)
            self.arrays[arr][idx] = self.get_val(parts[3])
        elif cmd == "ARRAYINSERT":
            arr,idx=parts[1].lower(),int(self.num(parts[2]))
            self.arrays.setdefault(arr,[]).insert(idx, self.get_val(parts[3]))
        elif cmd == "ARRAYREMOVE":
            arr,idx=parts[1].lower(),int(self.num(parts[2]))
            if self.arrays.get(arr) and 0<=idx<len(self.arrays[arr]):
                self.arrays[arr].pop(idx)
        elif cmd == "ARRAYLEN":   self.vars[parts[1].lower()] = len(self.arrays.get(parts[2].lower(),[]))
        elif cmd == "ARRAYCLEAR": self.arrays[parts[1].lower()] = []
        elif cmd == "ARRAYCOPY":  self.arrays[parts[1].lower()] = list(self.arrays.get(parts[2].lower(),[]))
        elif cmd == "ARRAYSORT":  self.arrays.setdefault(parts[1].lower(),[]).sort(key=lambda x:(isinstance(x,str),x))
        elif cmd == "ARRAYSORTREV": self.arrays.setdefault(parts[1].lower(),[]).sort(key=lambda x:(isinstance(x,str),x),reverse=True)
        elif cmd == "ARRAYREV":   self.arrays.setdefault(parts[1].lower(),[]).reverse()
        elif cmd == "ARRAYFILL":
            n,val=int(self.num(parts[2])),self.get_val(parts[3])
            self.arrays[parts[1].lower()] = [val]*n
        elif cmd == "ARRAYJOIN":
            sep=str(self.get_val(parts[3])) if len(parts)>3 else ","
            self.vars[parts[1].lower()] = sep.join(str(x) for x in self.arrays.get(parts[2].lower(),[]))
        elif cmd == "ARRAYSUM":
            self.vars[parts[1].lower()] = sum(float(x) for x in self.arrays.get(parts[2].lower(),[]) if str(x).replace(".","",1).lstrip("-").isdigit())
        elif cmd == "ARRAYMIN":
            lst=[float(x) for x in self.arrays.get(parts[2].lower(),[]) if str(x).replace(".","",1).lstrip("-").isdigit()]
            self.vars[parts[1].lower()] = min(lst) if lst else 0
        elif cmd == "ARRAYMAX":
            lst=[float(x) for x in self.arrays.get(parts[2].lower(),[]) if str(x).replace(".","",1).lstrip("-").isdigit()]
            self.vars[parts[1].lower()] = max(lst) if lst else 0
        elif cmd == "ARRAYAVG":
            lst=[float(x) for x in self.arrays.get(parts[2].lower(),[]) if str(x).replace(".","",1).lstrip("-").isdigit()]
            self.vars[parts[1].lower()] = sum(lst)/len(lst) if lst else 0
        elif cmd == "SHUFFLE":    random.shuffle(self.arrays.setdefault(parts[1].lower(),[]))
        elif cmd == "ARRAYCONTAINS":
            arr=self.arrays.get(parts[2].lower(),[])
            val=self.get_val(parts[3])
            self.vars[parts[1].lower()] = 1 if val in arr or str(val) in [str(x) for x in arr] else 0
        elif cmd == "ARRAYSLICE":
            arr=self.arrays.get(parts[2].lower(),[]); a,b=int(self.num(parts[3])),int(self.num(parts[4]))
            self.arrays[parts[1].lower()] = arr[a:b]

        # ── DICTS ─────────────────────────────────────────────────────────
        elif cmd == "DICTNEW":    self.dicts[parts[1].lower()] = {}
        elif cmd == "DICTSET":
            d,k,v = parts[1].lower(),str(self.get_val(parts[2])),self.get_val(parts[3])
            self.dicts.setdefault(d,{})[k] = v
        elif cmd == "DICTGET":
            d,k=parts[2].lower(),str(self.get_val(parts[3]))
            self.vars[parts[1].lower()] = self.dicts.get(d,{}).get(k,0)
        elif cmd == "DICTDEL":
            d,k=parts[1].lower(),str(self.get_val(parts[2]))
            self.dicts.get(d,{}).pop(k,None)
        elif cmd == "DICTHAS":
            d,k=parts[2].lower(),str(self.get_val(parts[3]))
            self.vars[parts[1].lower()] = 1 if k in self.dicts.get(d,{}) else 0
        elif cmd == "DICTKEYS":
            d=parts[2].lower()
            self.arrays[parts[1].lower()] = list(self.dicts.get(d,{}).keys())
        elif cmd == "DICTLEN":
            self.vars[parts[1].lower()] = len(self.dicts.get(parts[2].lower(),{}))
        elif cmd == "DICTCLEAR":  self.dicts[parts[1].lower()] = {}
        elif cmd == "DICTTOJSON":
            d=parts[2].lower()
            self.vars[parts[1].lower()] = json.dumps(self.dicts.get(d,{}))
        elif cmd == "JSONTODECT":
            try: self.dicts[parts[1].lower()] = json.loads(str(self.get_val(parts[2])))
            except: pass

        # ── FLOW ──────────────────────────────────────────────────────────
        elif cmd == "GOTO":
            lbl=parts[1].lower()
            if lbl in self.labels: self.pc=self.labels[lbl]; J=True
        elif cmd == "CALL":
            lbl=parts[1].lower()
            if lbl in self.labels: self.call_stack.append(self.pc+1); self.pc=self.labels[lbl]; J=True
        elif cmd == "RETURN":
            if self.call_stack: self.pc=self.call_stack.pop(); J=True
        elif cmd == "IFEQ":
            if str(self.get_val(parts[1]))!=str(self.get_val(parts[2])): self.pc+=1
        elif cmd == "IFNEQ":
            if str(self.get_val(parts[1]))==str(self.get_val(parts[2])): self.pc+=1
        elif cmd == "IFGT":
            if self.num(parts[1])<=self.num(parts[2]): self.pc+=1
        elif cmd == "IFLT":
            if self.num(parts[1])>=self.num(parts[2]): self.pc+=1
        elif cmd == "IFGTE":
            if self.num(parts[1])<self.num(parts[2]): self.pc+=1
        elif cmd == "IFLTE":
            if self.num(parts[1])>self.num(parts[2]): self.pc+=1
        elif cmd == "IFZERO":
            if self.num(parts[1])!=0: self.pc+=1
        elif cmd == "IFNOTZERO":
            if self.num(parts[1])==0: self.pc+=1
        elif cmd == "IFBETWEEN":
            v,lo,hi=self.num(parts[1]),self.num(parts[2]),self.num(parts[3])
            if not (lo<=v<=hi): self.pc+=1
        elif cmd == "IFKEY":
            k=parts[1].lower(); lbl=parts[2].lower()
            if k in self.key_held and lbl in self.labels: self.pc=self.labels[lbl]; J=True
        elif cmd == "IFKEYPRESSED":
            k=parts[1].lower(); lbl=parts[2].lower()
            if k in self.key_just_pressed and lbl in self.labels: self.pc=self.labels[lbl]; J=True
        elif cmd == "IFKEYRELEASED":
            k=parts[1].lower(); lbl=parts[2].lower()
            if k in self.key_just_released and lbl in self.labels: self.pc=self.labels[lbl]; J=True
        elif cmd == "IFMOUSEDOWN":
            btn=parts[1].lower(); lbl=parts[2].lower()
            if btn in self.mouse_held and lbl in self.labels: self.pc=self.labels[lbl]; J=True
        elif cmd == "GETKEY":
            self.vars[parts[1].lower()] = self.vars["last_key"]; self.vars["last_key"]="None"
        elif cmd == "KEYDOWN":
            self.vars[parts[2].lower()] = 1 if parts[1].lower() in self.key_held else 0
        elif cmd == "CLEARKEYS":  self.key_held.clear(); self.key_just_pressed.clear()
        elif cmd == "WAITKEY":
            self.vars["last_key"]="None"
            while self.vars["last_key"]=="None" and self.running:
                self.root.update(); time.sleep(0.01)
            self.vars[parts[1].lower()] = self.vars["last_key"]
        elif cmd == "WAITCLICK":
            self.waiting=True
            while self.waiting and self.running: self.root.update(); time.sleep(0.01)
        elif cmd == "WAIT":    self.root.update(); time.sleep(self.num(parts[1]))
        elif cmd == "PAUSE":   self.paused=True
        elif cmd == "RESUME":  self.paused=False
        elif cmd == "SKIP":    self.pc+=int(self.num(parts[1])); J=True
        elif cmd == "STOP":    self.running=False
        elif cmd == "NOP":     pass
        elif cmd == "EXIT":    self.running=False; self.root.destroy(); sys.exit(0)
        elif cmd == "ON":
            event=parts[1].lower(); lbl=parts[2].lower()
            self.event_handlers[event]=lbl

        # ── MOUSE ─────────────────────────────────────────────────────────
        elif cmd == "GETMOUSE":
            self.vars[parts[1].lower()]=self.vars["mouse_x"]
            self.vars[parts[2].lower()]=self.vars["mouse_y"]
        elif cmd == "MOUSECLICKED": self.vars[parts[1].lower()]=self.vars["mouse_clicked"]
        elif cmd == "MOUSEDOWN":    self.vars[parts[1].lower()] = 1 if parts[2].lower() in self.mouse_held else 0
        elif cmd == "IFMOUSE":
            x1,y1,x2,y2=self.num(parts[1]),self.num(parts[2]),self.num(parts[3]),self.num(parts[4])
            lbl=parts[5].lower(); mx,my=self.vars["mouse_x"],self.vars["mouse_y"]
            if x1<=mx<=x2 and y1<=my<=y2 and lbl in self.labels: self.pc=self.labels[lbl]; J=True
        elif cmd == "IFCLICKED":
            x1,y1,x2,y2=self.num(parts[1]),self.num(parts[2]),self.num(parts[3]),self.num(parts[4])
            lbl=parts[5].lower(); mx,my=self.vars["mouse_x"],self.vars["mouse_y"]
            if self.vars["mouse_clicked"] and x1<=mx<=x2 and y1<=my<=y2 and lbl in self.labels:
                self.pc=self.labels[lbl]; J=True

        # ── GRAPHICS ──────────────────────────────────────────────────────
        elif cmd == "BG":
            c=parts[1]; self.bg_color=c; self.canvas.config(bg=c); self.root.config(bg=c)
        elif cmd == "GRADIENT":
            if HAS_PIL:
                w,h=self.canvas.winfo_width(),self.canvas.winfo_height()
                if w<1: w=700
                if h<1: h=450
                c1=parts[1].lstrip("#"); c2=parts[2].lstrip("#"); axis=parts[3].lower() if len(parts)>3 else "v"
                img=Image.new("RGB",(w,h))
                r1,g1,b1=int(c1[0:2],16),int(c1[2:4],16),int(c1[4:6],16)
                r2,g2,b2=int(c2[0:2],16),int(c2[2:4],16),int(c2[4:6],16)
                for i in range(h if axis=="v" else w):
                    t=i/(h-1 if axis=="v" else w-1) if (h>1 and w>1) else 0
                    cr,cg,cb=int(r1+(r2-r1)*t),int(g1+(g2-g1)*t),int(b1+(b2-b1)*t)
                    if axis=="v": img.paste((cr,cg,cb),(0,i,w,i+1))
                    else: img.paste((cr,cg,cb),(i,0,i+1,h))
                self._bg_img=ImageTk.PhotoImage(img)
                self.canvas.create_image(0,0,image=self._bg_img,anchor="nw",tags="__bg")
                self.canvas.tag_lower("__bg")
        elif cmd == "CLEAR":
            self.canvas.delete("all"); self.sprites.clear(); self.sprite_data.clear()
        elif cmd == "CLEARSPRITES":
            self.canvas.delete("all"); self.sprites.clear()
        elif cmd == "FLASH":
            curr=self.canvas.cget("bg")
            self.canvas.config(bg="white"); self.root.update(); time.sleep(0.05)
            self.canvas.config(bg=curr); self.root.update()
        elif cmd == "SHAKE":
            self._shake_frames=int(self.num(parts[1]) if len(parts)>1 else 10)
            self._shake_intensity=int(self.num(parts[2]) if len(parts)>2 else 5)
        elif cmd == "DRAWBOX":
            sid=parts[1]; x,y,s,c=self.num(parts[2]),self.num(parts[3]),self.num(parts[4]),parts[5]
            outline=parts[6] if len(parts)>6 else ""
            self.sprites[sid]=self.canvas.create_rectangle(x,y,x+s,y+s,fill=c,outline=outline)
            self.sprite_data[sid]={"x":x,"y":y,"w":s,"h":s,"vx":0,"vy":0,"angle":0}
        elif cmd == "DRAWRECT":
            sid=parts[1]; x,y,w,h,c=self.num(parts[2]),self.num(parts[3]),self.num(parts[4]),self.num(parts[5]),parts[6]
            outline=parts[7] if len(parts)>7 else ""
            self.sprites[sid]=self.canvas.create_rectangle(x,y,x+w,y+h,fill=c,outline=outline)
            self.sprite_data[sid]={"x":x,"y":y,"w":w,"h":h,"vx":0,"vy":0,"angle":0}
        elif cmd == "DRAWROUNDRECT":
            sid=parts[1]; x,y,w,h,r,c=self.num(parts[2]),self.num(parts[3]),self.num(parts[4]),self.num(parts[5]),self.num(parts[6]),parts[7]
            self.sprites[sid]=self.canvas.create_oval(x,y,x+w,y+h,fill=c,outline="")
            self.sprite_data[sid]={"x":x,"y":y,"w":w,"h":h,"vx":0,"vy":0,"angle":0}
        elif cmd == "DRAWCIRCLE":
            sid=parts[1]; x,y,r,c=self.num(parts[2]),self.num(parts[3]),self.num(parts[4]),parts[5]
            self.sprites[sid]=self.canvas.create_oval(x,y,x+r,y+r,fill=c,outline="")
            self.sprite_data[sid]={"x":x,"y":y,"w":r,"h":r,"vx":0,"vy":0,"angle":0}
        elif cmd == "DRAWOVAL":
            sid=parts[1]; x,y,w,h,c=self.num(parts[2]),self.num(parts[3]),self.num(parts[4]),self.num(parts[5]),parts[6]
            self.sprites[sid]=self.canvas.create_oval(x,y,x+w,y+h,fill=c,outline="")
            self.sprite_data[sid]={"x":x,"y":y,"w":w,"h":h,"vx":0,"vy":0,"angle":0}
        elif cmd == "DRAWLINE":
            sid=parts[1]; x1,y1,x2,y2,c=self.num(parts[2]),self.num(parts[3]),self.num(parts[4]),self.num(parts[5]),parts[6]
            lw=int(self.num(parts[7])) if len(parts)>7 else 1
            self.sprites[sid]=self.canvas.create_line(x1,y1,x2,y2,fill=c,width=lw)
        elif cmd == "DRAWARROW":
            sid=parts[1]; x1,y1,x2,y2,c=self.num(parts[2]),self.num(parts[3]),self.num(parts[4]),self.num(parts[5]),parts[6]
            self.sprites[sid]=self.canvas.create_line(x1,y1,x2,y2,fill=c,width=2,arrow=tk.LAST)
        elif cmd == "DRAWPOLY":
            sid,c=parts[1],parts[2]; coords=[self.num(p) for p in parts[3:]]
            self.sprites[sid]=self.canvas.create_polygon(*coords,fill=c,outline="")
        elif cmd == "DRAWTEXT":
            msg=self.resolve_str(self.extract_string(active))
            color=parts[-3] if len(parts)>=4 else "#ffffff"
            x,y=self.num(parts[-2]),self.num(parts[-1])
            fs=int(self.num(parts[-4])) if len(parts)>=5 else 16
            self.canvas.create_text(x,y,text=msg,fill=color,font=("Arial",fs))
        elif cmd == "DRAWLABEL":
            sid=parts[1]; msg=self.resolve_str(self.extract_string(active))
            color=parts[-3]; x,y=self.num(parts[-2]),self.num(parts[-1])
            fs=int(self.num(parts[-4])) if len(parts)>=7 else 14
            self.sprites[sid]=self.canvas.create_text(x,y,text=msg,fill=color,font=("Arial",fs))
        elif cmd == "DRAWIMAGE":
            sid=parts[1]; path=str(self.get_val(parts[2]))
            x,y=self.num(parts[3]),self.num(parts[4])
            full=resource_path("assets", path) if not os.path.isabs(path) else path
            if not os.path.exists(full): full=path
            if HAS_PIL and os.path.exists(full):
                try:
                    img=Image.open(full)
                    if len(parts)>6: img=img.resize((int(self.num(parts[5])),int(self.num(parts[6]))),Image.LANCZOS)
                    tk_img=ImageTk.PhotoImage(img)
                    self.sprite_images[sid]=tk_img
                    self.sprites[sid]=self.canvas.create_image(x,y,image=tk_img,anchor="nw")
                    self.sprite_data[sid]={"x":x,"y":y,"w":img.width,"h":img.height,"vx":0,"vy":0,"angle":0}
                except Exception as ex: self.log(f"DRAWIMAGE: {ex}")
            else:
                w=int(self.num(parts[5])) if len(parts)>5 else 32
                h=int(self.num(parts[6])) if len(parts)>6 else 32
                self.sprites[sid]=self.canvas.create_rectangle(x,y,x+w,y+h,fill="#8844aa",outline="#cc88ff")
                self.sprite_data[sid]={"x":x,"y":y,"w":w,"h":h,"vx":0,"vy":0,"angle":0}
        elif cmd == "DRAWTILE":
            # DRAWTILE id path x y tile_x tile_y tile_w tile_h [dest_w dest_h]
            sid=parts[1]; path=str(self.get_val(parts[2]))
            x,y=self.num(parts[3]),self.num(parts[4])
            tx,ty,tw,th=int(self.num(parts[5])),int(self.num(parts[6])),int(self.num(parts[7])),int(self.num(parts[8]))
            full=resource_path("assets",path) if not os.path.isabs(path) else path
            if HAS_PIL and os.path.exists(full):
                try:
                    img=Image.open(full).crop((tx,ty,tx+tw,ty+th))
                    if len(parts)>10: img=img.resize((int(self.num(parts[9])),int(self.num(parts[10]))),Image.NEAREST)
                    tk_img=ImageTk.PhotoImage(img)
                    self.sprite_images[sid]=tk_img
                    self.sprites[sid]=self.canvas.create_image(x,y,image=tk_img,anchor="nw")
                    self.sprite_data[sid]={"x":x,"y":y,"w":img.width,"h":img.height,"vx":0,"vy":0,"angle":0}
                except Exception as ex: self.log(f"DRAWTILE: {ex}")
        elif cmd == "SETANIM":
            # SETANIM id frame_dir pattern interval   (e.g. SETANIM player ./frames walk_*.png 0.1)
            sid=parts[1]; folder=str(self.get_val(parts[2]))
            pattern=str(self.get_val(parts[3])) if len(parts)>3 else "*.png"
            interval=self.num(parts[4]) if len(parts)>4 else 0.1
            frames=sorted(glob.glob(os.path.join(folder,pattern)))
            if frames:
                self.sprite_anims[sid]={"frames":frames,"frame_idx":0,"interval":interval,"last_t":time.time()}
        elif cmd == "STOPANIM":  self.sprite_anims.pop(parts[1],None)
        elif cmd == "MOVE":
            sid=parts[1]; dx,dy=self.num(parts[2]),self.num(parts[3])
            if sid in self.sprites:
                self.canvas.move(self.sprites[sid],dx,dy)
                if sid in self.sprite_data: self.sprite_data[sid]["x"]+=dx; self.sprite_data[sid]["y"]+=dy
        elif cmd == "MOVETO":
            sid=parts[1]; tx,ty=self.num(parts[2]),self.num(parts[3])
            if sid in self.sprites and sid in self.sprite_data:
                d=self.sprite_data[sid]; dx=tx-d["x"]; dy=ty-d["y"]
                self.canvas.move(self.sprites[sid],dx,dy); d["x"]=tx; d["y"]=ty
        elif cmd == "SETPOS":
            sid=parts[1]; tx,ty=self.num(parts[2]),self.num(parts[3])
            if sid in self.sprites and sid in self.sprite_data:
                d=self.sprite_data[sid]; dx=tx-d["x"]; dy=ty-d["y"]
                self.canvas.move(self.sprites[sid],dx,dy); d["x"]=tx; d["y"]=ty
        elif cmd == "GETPOS":
            sid=parts[1]
            if sid in self.sprite_data:
                self.vars[parts[2].lower()]=self.sprite_data[sid]["x"]
                self.vars[parts[3].lower()]=self.sprite_data[sid]["y"]
        elif cmd == "GETSIZE":
            sid=parts[1]
            if sid in self.sprite_data:
                self.vars[parts[2].lower()]=self.sprite_data[sid]["w"]
                self.vars[parts[3].lower()]=self.sprite_data[sid]["h"]
        elif cmd == "RECOLOR":
            sid=parts[1]; c=parts[2]
            if sid in self.sprites:
                try: self.canvas.itemconfig(self.sprites[sid],fill=c)
                except: pass
        elif cmd == "REOUTLINE":
            sid=parts[1]; c=parts[2]
            if sid in self.sprites:
                try: self.canvas.itemconfig(self.sprites[sid],outline=c)
                except: pass
        elif cmd == "SETWIDTH":
            sid=parts[1]; w=int(self.num(parts[2]))
            if sid in self.sprites:
                try: self.canvas.itemconfig(self.sprites[sid],width=w)
                except: pass
        elif cmd == "SETALPHA":
            pass  # tkinter canvas doesn't support per-item alpha natively
        elif cmd == "HIDE":
            sid=parts[1]
            if sid in self.sprites: self.canvas.itemconfig(self.sprites[sid],state="hidden")
        elif cmd == "SHOW":
            sid=parts[1]
            if sid in self.sprites: self.canvas.itemconfig(self.sprites[sid],state="normal")
        elif cmd == "DELETE":
            sid=parts[1]
            if sid in self.sprites:
                self.canvas.delete(self.sprites[sid]); del self.sprites[sid]
                self.sprite_data.pop(sid,None); self.sprite_images.pop(sid,None)
        elif cmd == "SCALE":
            sid=parts[1]; f=self.num(parts[2])
            if sid in self.sprite_data: d=self.sprite_data[sid]; d["w"]*=f; d["h"]*=f
        elif cmd == "LAYER":
            sid=parts[1]
            if sid in self.sprites:
                if parts[2].lower()=="above": self.canvas.lift(self.sprites[sid])
                else: self.canvas.lower(self.sprites[sid])
        elif cmd == "UPDATETEXT":
            sid=parts[1]; msg=self.resolve_str(self.extract_string(active))
            if sid in self.sprites:
                try: self.canvas.itemconfig(self.sprites[sid],text=msg)
                except: pass
        elif cmd == "COPYSPRITE":
            src=parts[1]; dst=parts[2]
            if src in self.sprite_data:
                d=copy.copy(self.sprite_data[src])
                self.sprite_data[dst]=d
        elif cmd == "SPRITEEXISTS":
            self.vars[parts[1].lower()] = 1 if parts[2] in self.sprites else 0

        # ── SPRITE PHYSICS ────────────────────────────────────────────────
        elif cmd == "SETVEL":
            sid=parts[1]
            if sid in self.sprite_data:
                self.sprite_data[sid]["vx"]=self.num(parts[2])
                self.sprite_data[sid]["vy"]=self.num(parts[3])
        elif cmd == "ADDVEL":
            sid=parts[1]
            if sid in self.sprite_data:
                self.sprite_data[sid]["vx"]=self.sprite_data[sid].get("vx",0)+self.num(parts[2])
                self.sprite_data[sid]["vy"]=self.sprite_data[sid].get("vy",0)+self.num(parts[3])
        elif cmd == "GETVEL":
            sid=parts[1]
            if sid in self.sprite_data:
                self.vars[parts[2].lower()]=self.sprite_data[sid].get("vx",0)
                self.vars[parts[3].lower()]=self.sprite_data[sid].get("vy",0)
        elif cmd == "APPLYVEL":
            for sid,d in list(self.sprite_data.items()):
                vx=d.get("vx",0); vy=d.get("vy",0)
                if vx or vy:
                    d["x"]+=vx; d["y"]+=vy
                    if sid in self.sprites: self.canvas.move(self.sprites[sid],vx,vy)
        elif cmd == "APPLYVELONE":
            sid=parts[1]
            if sid in self.sprite_data:
                d=self.sprite_data[sid]; vx=d.get("vx",0); vy=d.get("vy",0)
                d["x"]+=vx; d["y"]+=vy
                if sid in self.sprites: self.canvas.move(self.sprites[sid],vx,vy)
        elif cmd == "APPLYGRAV":
            g=self.num(parts[1]) if len(parts)>1 else 0.5
            for sid,d in list(self.sprite_data.items()):
                d["vy"]=d.get("vy",0)+g
        elif cmd == "APPLYDRAG":
            drag=self.num(parts[1]) if len(parts)>1 else 0.95
            for sid,d in list(self.sprite_data.items()):
                d["vx"]=d.get("vx",0)*drag; d["vy"]=d.get("vy",0)*drag
        elif cmd == "MOVETOWARD":
            sid=parts[1]; tx,ty=self.num(parts[2]),self.num(parts[3]); spd=self.num(parts[4])
            if sid in self.sprite_data:
                d=self.sprite_data[sid]; dx=tx-d["x"]; dy=ty-d["y"]; dist=math.hypot(dx,dy)
                if dist>0: ratio=min(spd,dist)/dist; d["x"]+=dx*ratio; d["y"]+=dy*ratio
                if sid in self.sprites: self.canvas.coords(self.sprites[sid],d["x"],d["y"],d["x"]+d["w"],d["y"]+d["h"])

        # ── CAMERA ────────────────────────────────────────────────────────
        elif cmd == "CAMPOS":   self._camera_x=self.num(parts[1]); self._camera_y=self.num(parts[2])
        elif cmd == "CAMZOOM":  self._camera_zoom=self.num(parts[1])
        elif cmd == "GETCAMP":  self.vars[parts[1].lower()]=self._camera_x; self.vars[parts[2].lower()]=self._camera_y
        elif cmd == "CAMFOLLOW":
            sid=parts[1]; lerp=self.num(parts[2]) if len(parts)>2 else 0.1
            if sid in self.sprite_data:
                d=self.sprite_data[sid]
                cx=d["x"]-self.vars["canvas_w"]/2; cy=d["y"]-self.vars["canvas_h"]/2
                self._camera_x+=(cx-self._camera_x)*lerp
                self._camera_y+=(cy-self._camera_y)*lerp

        # ── PARTICLES ─────────────────────────────────────────────────────
        elif cmd == "BURST":
            pid=parts[1]; x,y=self.num(parts[2]),self.num(parts[3])
            count=int(self.num(parts[4])); color=parts[5]
            size=self.num(parts[6]) if len(parts)>6 else 4
            speed=self.num(parts[7]) if len(parts)>7 else 3
            gravity=self.num(parts[8]) if len(parts)>8 else 0.2
            drag=self.num(parts[9]) if len(parts)>9 else 1.0
            life=random.randint(20,60)
            self.particles.setdefault(pid,[])
            for _ in range(count):
                angle=random.uniform(0,math.tau); spd=random.uniform(speed*0.5,speed)
                cid=self.canvas.create_oval(x,y,x+size,y+size,fill=color,outline="")
                self.particles[pid].append({"x":x,"y":y,"vx":math.cos(angle)*spd,"vy":math.sin(angle)*spd,
                    "life":life,"max_life":life,"size":size,"gravity":gravity,"drag":drag,"cid":cid})
        elif cmd == "STREAM":
            pid=parts[1]; x,y=self.num(parts[2]),self.num(parts[3])
            direction=self.num(parts[4]); color=parts[5]; count=int(self.num(parts[6])) if len(parts)>6 else 5
            drag=self.num(parts[7]) if len(parts)>7 else 1.0
            self.particles.setdefault(pid,[])
            for _ in range(count):
                angle=math.radians(direction)+random.uniform(-0.3,0.3); spd=random.uniform(1,4)
                cid=self.canvas.create_oval(x,y,x+3,y+3,fill=color,outline="")
                life=random.randint(15,35)
                self.particles[pid].append({"x":x,"y":y,"vx":math.cos(angle)*spd,"vy":math.sin(angle)*spd,
                    "life":life,"max_life":life,"size":3,"gravity":0.1,"drag":drag,"cid":cid})
        elif cmd == "EXPLOSION":
            pid=parts[1]; x,y=self.num(parts[2]),self.num(parts[3]); color=parts[4]
            rings=int(self.num(parts[5])) if len(parts)>5 else 3
            self.particles.setdefault(pid,[])
            for ring in range(rings):
                count=12+ring*8; radius=(ring+1)*3
                for i in range(count):
                    angle=i*(math.tau/count); spd=radius*0.4+random.uniform(0,2)
                    size=max(1,5-ring); life=30+ring*5
                    cid=self.canvas.create_oval(x,y,x+size,y+size,fill=color,outline="")
                    self.particles[pid].append({"x":x,"y":y,"vx":math.cos(angle)*spd,"vy":math.sin(angle)*spd,
                        "life":life,"max_life":life,"size":size,"gravity":0.05,"drag":0.96,"cid":cid})
        elif cmd == "CLEARPARTICLES":
            pid=parts[1]
            for p in self.particles.get(pid,[]):
                try: self.canvas.delete(p["cid"])
                except: pass
            self.particles[pid]=[]
        elif cmd == "PARTICLECOUNT": self.vars[parts[2].lower()]=len(self.particles.get(parts[1],[]))
        elif cmd == "SETGRAVITY":
            pid=parts[1]; g=self.num(parts[2])
            for p in self.particles.get(pid,[]): p["gravity"]=g
        elif cmd == "SETPARTICLEDRAG":
            pid=parts[1]; d=self.num(parts[2])
            for p in self.particles.get(pid,[]): p["drag"]=d
        elif cmd == "SETPARTICLELIFE":
            pid=parts[1]; life=int(self.num(parts[2]))
            for p in self.particles.get(pid,[]): p["life"]=life

        # ── TWEENING ──────────────────────────────────────────────────────
        elif cmd == "TWEEN":
            tid=parts[1]; var=parts[2].lower(); frm,to=self.num(parts[3]),self.num(parts[4])
            dur=self.num(parts[5]); ease=parts[6].lower() if len(parts)>6 else "linear"
            then=parts[7].lower() if len(parts)>7 else None
            self.tweens[tid]={"var":var,"from":frm,"to":to,"duration":dur,"ease":ease,
                              "start":time.time(),"done":False,"then":then,"loop":False}
        elif cmd == "TWEENLOOP":
            tid=parts[1]; var=parts[2].lower(); frm,to=self.num(parts[3]),self.num(parts[4])
            dur=self.num(parts[5]); ease=parts[6].lower() if len(parts)>6 else "linear"
            self.tweens[tid]={"var":var,"from":frm,"to":to,"duration":dur,"ease":ease,
                              "start":time.time(),"done":False,"then":None,"loop":True}
        elif cmd == "TWEENDONE":
            tid,lbl=parts[1],parts[2].lower()
            if self.tweens.get(tid,{}).get("done") and lbl in self.labels: self.pc=self.labels[lbl]; J=True
        elif cmd == "STOPTWEEN":  self.tweens.pop(parts[1],None)
        elif cmd == "TWEENSPRITE":
            sid=parts[1]; prop=parts[2].lower(); to=self.num(parts[3]); dur=self.num(parts[4])
            ease=parts[5].lower() if len(parts)>5 else "easeinout"
            frm=self.sprite_data.get(sid,{}).get(prop,0) if prop in ("x","y","w","h") else 0
            self.vars[f"__ts_{sid}_{prop}"]=frm
            self.tweens[f"__ts_{sid}_{prop}"] = {"var":f"__ts_{sid}_{prop}","from":frm,"to":to,
                "duration":dur,"ease":ease,"start":time.time(),"done":False,"then":None,"loop":False}

        # ── TIMERS ────────────────────────────────────────────────────────
        elif cmd == "TIMER":
            self.timers[parts[1]]={"end":time.time()+self.num(parts[2]),"label":parts[3].lower(),
                                   "fired":False,"repeat":False}
        elif cmd == "TIMERPEAT":
            interval=self.num(parts[2])
            self.timers[parts[1]]={"end":time.time()+interval,"label":parts[3].lower(),
                                   "fired":False,"repeat":True,"interval":interval}
        elif cmd == "CANCELTIMER": self.timers.pop(parts[1],None)
        elif cmd == "TIMERDONE":
            t=self.timers.get(parts[1])
            if t and t.get("fired") and parts[2].lower() in self.labels:
                self.pc=self.labels[parts[2].lower()]; J=True
        elif cmd == "TIMELEFT":
            t=self.timers.get(parts[1])
            self.vars[parts[2].lower()]=max(0,round(t["end"]-time.time(),2)) if t else 0

        # ── COLLISION ─────────────────────────────────────────────────────
        elif cmd == "COLLIDE":
            sid1,sid2,rv=parts[1],parts[2],parts[3].lower(); self.vars[rv]=0
            if sid1 in self.sprite_data and sid2 in self.sprite_data:
                a=self.sprite_data[sid1]; b=self.sprite_data[sid2]
                if a["x"]<b["x"]+b["w"] and a["x"]+a["w"]>b["x"] and a["y"]<b["y"]+b["h"] and a["y"]+a["h"]>b["y"]:
                    self.vars[rv]=1
        elif cmd == "COLLIDECIRCLE":
            sid1,sid2,rv=parts[1],parts[2],parts[3].lower(); self.vars[rv]=0
            if sid1 in self.sprite_data and sid2 in self.sprite_data:
                a,b=self.sprite_data[sid1],self.sprite_data[sid2]
                cx1,cy1=a["x"]+a["w"]/2,a["y"]+a["h"]/2; cx2,cy2=b["x"]+b["w"]/2,b["y"]+b["h"]/2
                r1,r2=a["w"]/2,b["w"]/2
                if math.hypot(cx1-cx2,cy1-cy2)<r1+r2: self.vars[rv]=1
        elif cmd == "BOUNDRECT":
            sid=parts[1]; x1,y1,x2,y2=self.num(parts[2]),self.num(parts[3]),self.num(parts[4]),self.num(parts[5])
            rv=parts[6].lower(); self.vars[rv]=0
            if sid in self.sprite_data:
                d=self.sprite_data[sid]
                if d["x"]<x1: d["x"]=x1; self.vars[rv]=1
                if d["y"]<y1: d["y"]=y1; self.vars[rv]=1
                if d["x"]+d["w"]>x2: d["x"]=x2-d["w"]; self.vars[rv]=1
                if d["y"]+d["h"]>y2: d["y"]=y2-d["h"]; self.vars[rv]=1
        elif cmd == "COLLIDEPOINT":
            sid=parts[1]; px,py=self.num(parts[2]),self.num(parts[3]); rv=parts[4].lower()
            self.vars[rv]=0
            if sid in self.sprite_data:
                d=self.sprite_data[sid]
                if d["x"]<=px<=d["x"]+d["w"] and d["y"]<=py<=d["y"]+d["h"]: self.vars[rv]=1

        # ── SOUND ─────────────────────────────────────────────────────────
        elif cmd == "SOUND":   self.beep(self.num(parts[1]),self.num(parts[2]))
        elif cmd == "BEEP":    self.beep(440,100)
        elif cmd == "CHORD":
            ms=int(self.num(parts[-1]))
            for hz in parts[1:-1]: threading.Thread(target=self.beep,args=(self.num(hz),ms),daemon=True).start()
        elif cmd == "MELODY":
            notes=parts[1:]
            for i in range(0,len(notes)-1,2): self.beep(self.num(notes[i]),int(self.num(notes[i+1])))
        elif cmd == "SILENCE": pass

        # ── DIALOGS ───────────────────────────────────────────────────────
        elif cmd == "POPUP":     messagebox.showinfo("QUK",self.resolve_str(self.extract_string(active)))
        elif cmd == "ALERT":     messagebox.showwarning("QUK Alert",self.resolve_str(self.extract_string(active)))
        elif cmd == "ERROR":     messagebox.showerror("QUK Error",self.resolve_str(self.extract_string(active)))
        elif cmd == "CONFIRM":
            res=messagebox.askyesno("QUK",self.resolve_str(self.extract_string(active)))
            self.vars[parts[1].lower()]="yes" if res else "no"
        elif cmd == "PROMPT":
            res=simpledialog.askstring("QUK Input",self.resolve_str(self.extract_string(active))) or ""
            self.vars[parts[1].lower()]=res
        elif cmd == "PROMPTNUM":
            res=simpledialog.askfloat("QUK Input",self.resolve_str(self.extract_string(active))) or 0
            self.vars[parts[1].lower()]=res
        elif cmd == "PICKCOLOR":
            res=colorchooser.askcolor(title="Pick a color")
            self.vars[parts[1].lower()]=res[1] if res and res[1] else "#ffffff"
        elif cmd == "PICKFILE":
            res=filedialog.askopenfilename(title="Select File") or ""
            self.vars[parts[1].lower()]=res

        # ── WINDOW ────────────────────────────────────────────────────────
        elif cmd == "TITLE":       self.root.title(self.resolve_str(" ".join(parts[1:])))
        elif cmd == "RESIZE":      self.root.geometry(f"{int(self.num(parts[1]))}x{int(self.num(parts[2]))}")
        elif cmd == "FULLSCREEN":  self.root.attributes("-fullscreen",parts[1].lower()=="on")
        elif cmd == "TOPMOST":     self.root.attributes("-topmost",parts[1].lower()=="on")
        elif cmd == "CURSOR":      self.root.config(cursor=parts[1])
        elif cmd == "MINIMIZE":    self.root.iconify()
        elif cmd == "MAXIMIZE":    self.root.state("zoomed")
        elif cmd == "RESTORE":     self.root.state("normal")
        elif cmd == "CANVASSIZE":
            self.canvas.config(width=int(self.num(parts[1])),height=int(self.num(parts[2])))
            self.vars["canvas_w"]=int(self.num(parts[1])); self.vars["canvas_h"]=int(self.num(parts[2]))
        elif cmd == "SETBG":       self.root.configure(bg=parts[1])
        elif cmd == "OPACITY":
            try: self.root.attributes("-alpha",self.num(parts[1]))
            except: pass

        # ── SYSTEM ────────────────────────────────────────────────────────
        elif cmd == "TIME":      self.vars[parts[1].lower()]=datetime.datetime.now().strftime("%H:%M:%S")
        elif cmd == "DATE":      self.vars[parts[1].lower()]=datetime.datetime.now().strftime("%Y-%m-%d")
        elif cmd == "YEAR":      self.vars[parts[1].lower()]=datetime.datetime.now().year
        elif cmd == "MONTH":     self.vars[parts[1].lower()]=datetime.datetime.now().month
        elif cmd == "DAY":       self.vars[parts[1].lower()]=datetime.datetime.now().day
        elif cmd == "HOUR":      self.vars[parts[1].lower()]=datetime.datetime.now().hour
        elif cmd == "MINUTE":    self.vars[parts[1].lower()]=datetime.datetime.now().minute
        elif cmd == "SECOND":    self.vars[parts[1].lower()]=datetime.datetime.now().second
        elif cmd == "TIMESTAMP": self.vars[parts[1].lower()]=int(time.time())
        elif cmd == "UPTIME":    self.vars[parts[1].lower()]=round(self.vars["time"],2)
        elif cmd == "WEB":       webbrowser.open(parts[1].strip('"'))
        elif cmd == "SHELL":     os.system(" ".join(parts[1:]))
        elif cmd == "GETENV":    self.vars[parts[1].lower()]=os.environ.get(parts[2],"")
        elif cmd == "HOSTNAME":  self.vars[parts[1].lower()]=socket.gethostname()
        elif cmd == "PLATFORM":  self.vars[parts[1].lower()]=platform.system()
        elif cmd == "EXEPATH":   self.vars[parts[1].lower()]=sys.executable
        elif cmd == "SCRIPTDIR": self.vars[parts[1].lower()]=os.path.dirname(os.path.abspath(self.file_path))

        # ── FILE I/O ──────────────────────────────────────────────────────
        elif cmd == "FILEWRITE":
            path=str(self.get_val(parts[1])); content=self.resolve_str(self.extract_string(active))
            with open(path,"w",encoding="utf-8") as f: f.write(content)
        elif cmd == "FILEAPPEND":
            path=str(self.get_val(parts[1])); content=self.resolve_str(self.extract_string(active))
            with open(path,"a",encoding="utf-8") as f: f.write(content+"\n")
        elif cmd == "FILEREAD":
            path=str(self.get_val(parts[2]))
            try:
                with open(path,"r",encoding="utf-8") as f: self.vars[parts[1].lower()]=f.read()
            except: self.vars[parts[1].lower()]=""
        elif cmd == "FILEEXISTS": self.vars[parts[1].lower()]=1 if os.path.exists(str(self.get_val(parts[2]))) else 0
        elif cmd == "FILEDELETE":
            try: os.remove(str(self.get_val(parts[1])))
            except: pass
        elif cmd == "FILELINES":
            path=str(self.get_val(parts[2]))
            try:
                with open(path,"r",encoding="utf-8") as f:
                    self.arrays[parts[1].lower()]=[l.rstrip("\n") for l in f]
            except: self.arrays[parts[1].lower()]=[]
        elif cmd == "FILECOPY":
            try: shutil.copy2(str(self.get_val(parts[1])),str(self.get_val(parts[2])))
            except: pass
        elif cmd == "MKDIR":
            try: os.makedirs(str(self.get_val(parts[1])),exist_ok=True)
            except: pass
        elif cmd == "LISTDIR":
            d=str(self.get_val(parts[2]))
            try: self.arrays[parts[1].lower()]=os.listdir(d)
            except: self.arrays[parts[1].lower()]=[]

        # ── SAVE / LOAD ───────────────────────────────────────────────────
        elif cmd == "SAVE":
            path=str(self.get_val(parts[1])) if len(parts)>1 else "quk_save.json"
            with open(path,"w") as f: json.dump(self.vars,f,default=str)
        elif cmd == "LOAD":
            path=str(self.get_val(parts[1])) if len(parts)>1 else "quk_save.json"
            if os.path.exists(path):
                with open(path,"r") as f: self.vars.update(json.load(f))
        elif cmd == "SAVEVAR":
            path=str(self.get_val(parts[1]))
            try:
                with open(path,"r") as f: d=json.load(f)
            except: d={}
            d[parts[2].lower()]=self.vars.get(parts[2].lower(),0)
            with open(path,"w") as f: json.dump(d,f)
        elif cmd == "LOADVAR":
            path=str(self.get_val(parts[1]))
            try:
                with open(path,"r") as f: d=json.load(f)
                self.vars[parts[2].lower()]=d.get(parts[2].lower(),0)
            except: pass
        elif cmd == "SAVEJSON":
            path=str(self.get_val(parts[1])); dname=parts[2].lower()
            with open(path,"w") as f: json.dump(self.dicts.get(dname,{}),f,indent=2)
        elif cmd == "LOADJSON":
            path=str(self.get_val(parts[2]))
            try:
                with open(path,"r") as f: self.dicts[parts[1].lower()]=json.load(f)
            except: pass

        # ── COLOR UTILS ───────────────────────────────────────────────────
        elif cmd == "RGB2HEX":
            r,g,b=int(self.num(parts[2])),int(self.num(parts[3])),int(self.num(parts[4]))
            self.vars[parts[1].lower()]=f"#{r:02x}{g:02x}{b:02x}"
        elif cmd == "HEX2RGB":
            h=str(self.get_val(parts[2])).lstrip("#")
            r,g,b=int(h[0:2],16),int(h[2:4],16),int(h[4:6],16)
            self.vars[parts[1].lower()+"_r"]=r; self.vars[parts[1].lower()+"_g"]=g; self.vars[parts[1].lower()+"_b"]=b
        elif cmd == "LERPCOLOR":
            h1=str(self.get_val(parts[2])).lstrip("#"); h2=str(self.get_val(parts[3])).lstrip("#"); t=self.num(parts[4])
            r=int(int(h1[0:2],16)*(1-t)+int(h2[0:2],16)*t)
            g=int(int(h1[2:4],16)*(1-t)+int(h2[2:4],16)*t)
            b=int(int(h1[4:6],16)*(1-t)+int(h2[4:6],16)*t)
            self.vars[parts[1].lower()]=f"#{r:02x}{g:02x}{b:02x}"
        elif cmd == "HSV2HEX":
            h,s,v=self.num(parts[2])/360,self.num(parts[3]),self.num(parts[4])
            r,g,b=[int(x*255) for x in colorsys.hsv_to_rgb(h,s,v)]
            self.vars[parts[1].lower()]=f"#{r:02x}{g:02x}{b:02x}"
        elif cmd == "RANDOMCOLOR":
            r,g,b=random.randint(0,255),random.randint(0,255),random.randint(0,255)
            self.vars[parts[1].lower()]=f"#{r:02x}{g:02x}{b:02x}"
        elif cmd == "RANDOMHUE":
            h=random.random()
            r,g,b=[int(x*255) for x in colorsys.hsv_to_rgb(h,1,1)]
            self.vars[parts[1].lower()]=f"#{r:02x}{g:02x}{b:02x}"
        elif cmd == "DARKEN":
            h=str(self.get_val(parts[2])).lstrip("#"); f=self.num(parts[3])
            r,g,b=[max(0,int(int(h[i*2:i*2+2],16)*f)) for i in range(3)]
            self.vars[parts[1].lower()]=f"#{r:02x}{g:02x}{b:02x}"
        elif cmd == "LIGHTEN":
            h=str(self.get_val(parts[2])).lstrip("#"); f=self.num(parts[3])
            r,g,b=[min(255,int(int(h[i*2:i*2+2],16)*f)) for i in range(3)]
            self.vars[parts[1].lower()]=f"#{r:02x}{g:02x}{b:02x}"
        elif cmd == "INVERTCOLOR":
            h=str(self.get_val(parts[2])).lstrip("#")
            r,g,b=255-int(h[0:2],16),255-int(h[2:4],16),255-int(h[4:6],16)
            self.vars[parts[1].lower()]=f"#{r:02x}{g:02x}{b:02x}"

        # ── DEBUG ─────────────────────────────────────────────────────────
        elif cmd == "PRINT":    print(self.resolve_str(" ".join(parts[1:])))
        elif cmd == "LOG":      self.log(self.resolve_str(" ".join(parts[1:])))
        elif cmd == "DEBUGON":  self.debug_mode=True
        elif cmd == "DEBUGOFF": self.debug_mode=False
        elif cmd == "ASSERT":
            if self.num(parts[1])==0:
                messagebox.showerror("Assert Failed",self.resolve_str(self.extract_string(active)))
        elif cmd == "DUMPVARS":
            print("\n=== QUK VAR DUMP ===")
            for k,v in sorted(self.vars.items()): print(f"  {k} = {v}")
        elif cmd == "DUMPSPRITES":
            print("\n=== QUK SPRITE DUMP ===")
            for k,v in self.sprite_data.items(): print(f"  {k}: {v}")
        elif cmd == "BENCHMARK": self.vars["fps_display"]=self.vars["fps"]
        elif cmd == "WATCH":     self.debug_watches.append(parts[1].lower())
        elif cmd == "STATSBAR":
            fps=int(self.vars["fps"]); fr=int(self.vars["frame"])
            self.update_status(f"FPS:{fps}  Frame:{fr}  Sprites:{len(self.sprites)}")

        # ── SCENES ────────────────────────────────────────────────────────
        elif cmd == "SCENE":
            lbl=parts[1].lower()
            if lbl in self.labels:
                self.canvas.delete("all"); self.sprites.clear(); self.sprite_data.clear()
                self.pc=self.labels[lbl]; J=True
        elif cmd == "SCENECLEAR":
            self.canvas.delete("all"); self.sprites.clear(); self.sprite_data.clear()

        # ── MISC ──────────────────────────────────────────────────────────
        elif cmd == "COPY":    self.vars[parts[1].lower()]=self.get_val(parts[2])
        elif cmd == "SWAP":
            a,b=parts[1].lower(),parts[2].lower()
            self.vars[a],self.vars[b]=self.vars.get(b,0),self.vars.get(a,0)
        elif cmd == "TOGGLE":  self.vars[parts[1].lower()]=0 if self.num(parts[1]) else 1
        elif cmd == "RANDSEED": random.seed(int(self.num(parts[1])))
        elif cmd == "FPS":
            target=self.num(parts[1])
            if target>0: time.sleep(max(0,(1.0/target)-self.vars["dt"]))
        elif cmd == "STATUSBAR": self.update_status(self.resolve_str(self.extract_string(active)))
        elif cmd == "CLIPBOARD":
            try: self.root.clipboard_clear(); self.root.clipboard_append(str(self.get_val(parts[1])))
            except: pass
        elif cmd == "TYPEOF":
            val=self.get_val(parts[2])
            t="number" if isinstance(val,(int,float)) else "string"
            self.vars[parts[1].lower()]=t
        elif cmd == "ISNUMBER":
            try: float(str(self.get_val(parts[2]))); self.vars[parts[1].lower()]=1
            except: self.vars[parts[1].lower()]=0
        else:
            self.log(f"Unknown cmd: {cmd} @ line {self.pc+1}")
        return J


# ═════════════════════════════════════════════════════════════════════════════
#  COMMAND REFERENCE (for the docs panel)
# ═════════════════════════════════════════════════════════════════════════════
COMMAND_DOCS = {
    "Math":     ["SET","ADD","SUB","MULT","DIV","IDIV","MOD","POW","SQRT","CBRT","ABS","NEG","INC","DEC",
                 "ROUND","FLOOR","CEIL","TRUNC","RAND","RANDF","RANDPICK","MIN","MAX","CLAMP",
                 "LERP","SMOOTHSTEP","SIN","COS","TAN","ASIN","ACOS","ATAN2","LOG","LOG2","LOG10","EXP",
                 "SIGN","DIST","ANGLE","NORM","MAP","WRAP","NOISE",
                 "BITAND","BITOR","BITXOR","BITNOT","LSHIFT","RSHIFT","HASH"],
    "Strings":  ["JOIN","UPPER","LOWER","REV","TRIM","LEN","SPLIT","SUBSTR","REPLACE","CONTAINS",
                 "STARTSWITH","ENDSWITH","INDEXOF","CHAR","ORD","PAD","REPEAT","FORMAT","TONUM","TOSTR",
                 "TOINT","B64ENC","B64DEC","REGEX","PRINTF","STRCOUNT"],
    "Arrays":   ["ARRAYNEW","ARRAYPUSH","ARRAYPOP","ARRAYSHIFT","ARRAYUNSHIFT","ARRAYGET","ARRAYSET",
                 "ARRAYINSERT","ARRAYREMOVE","ARRAYLEN","ARRAYCLEAR","ARRAYCOPY","ARRAYSORT",
                 "ARRAYSORTREV","ARRAYREV","ARRAYFILL","ARRAYJOIN","ARRAYSUM","ARRAYMIN","ARRAYMAX",
                 "ARRAYAVG","SHUFFLE","ARRAYCONTAINS","ARRAYSLICE"],
    "Dicts":    ["DICTNEW","DICTSET","DICTGET","DICTDEL","DICTHAS","DICTKEYS","DICTLEN","DICTCLEAR",
                 "DICTTOJSON","JSONTODECT"],
    "Flow":     ["GOTO","CALL","RETURN","IFEQ","IFNEQ","IFGT","IFLT","IFGTE","IFLTE","IFZERO",
                 "IFNOTZERO","IFBETWEEN","SKIP","STOP","NOP","EXIT","PAUSE","RESUME","ON"],
    "Input":    ["GETKEY","KEYDOWN","IFKEY","IFKEYPRESSED","IFKEYRELEASED","WAITKEY","CLEARKEYS",
                 "GETMOUSE","MOUSECLICKED","MOUSEDOWN","WAITCLICK","IFMOUSE","IFCLICKED","IFMOUSEDOWN"],
    "Graphics": ["BG","GRADIENT","CLEAR","CLEARSPRITES","FLASH","SHAKE",
                 "DRAWBOX","DRAWRECT","DRAWROUNDRECT","DRAWCIRCLE","DRAWOVAL","DRAWLINE","DRAWARROW",
                 "DRAWPOLY","DRAWTEXT","DRAWLABEL","DRAWIMAGE","DRAWTILE",
                 "MOVE","MOVETO","SETPOS","GETPOS","GETSIZE","RECOLOR","REOUTLINE","SETWIDTH",
                 "HIDE","SHOW","DELETE","SCALE","LAYER","UPDATETEXT","COPYSPRITE","SPRITEEXISTS"],
    "Sprites":  ["SETVEL","ADDVEL","GETVEL","APPLYVEL","APPLYVELONE","APPLYGRAV","APPLYDRAG",
                 "MOVETOWARD","SETANIM","STOPANIM"],
    "Camera":   ["CAMPOS","CAMZOOM","GETCAMP","CAMFOLLOW"],
    "Particles":["BURST","STREAM","EXPLOSION","CLEARPARTICLES","PARTICLECOUNT",
                 "SETGRAVITY","SETPARTICLEDRAG","SETPARTICLELIFE"],
    "Tweens":   ["TWEEN","TWEENLOOP","TWEENDONE","STOPTWEEN","TWEENSPRITE"],
    "Timers":   ["TIMER","TIMERPEAT","CANCELTIMER","TIMERDONE","TIMELEFT"],
    "Collision":["COLLIDE","COLLIDECIRCLE","BOUNDRECT","COLLIDEPOINT"],
    "Sound":    ["SOUND","BEEP","CHORD","MELODY","SILENCE"],
    "Dialogs":  ["POPUP","ALERT","ERROR","CONFIRM","PROMPT","PROMPTNUM","PICKCOLOR","PICKFILE"],
    "Window":   ["TITLE","RESIZE","FULLSCREEN","TOPMOST","CURSOR","MINIMIZE","MAXIMIZE","RESTORE",
                 "CANVASSIZE","SETBG","OPACITY","STATUSBAR"],
    "System":   ["TIME","DATE","YEAR","MONTH","DAY","HOUR","MINUTE","SECOND","TIMESTAMP","UPTIME",
                 "WEB","SHELL","GETENV","HOSTNAME","PLATFORM","EXEPATH","SCRIPTDIR"],
    "File I/O": ["FILEWRITE","FILEAPPEND","FILEREAD","FILEEXISTS","FILEDELETE","FILELINES",
                 "FILECOPY","MKDIR","LISTDIR"],
    "Save/Load":["SAVE","LOAD","SAVEVAR","LOADVAR","SAVEJSON","LOADJSON"],
    "Color":    ["RGB2HEX","HEX2RGB","LERPCOLOR","HSV2HEX","RANDOMCOLOR","RANDOMHUE",
                 "DARKEN","LIGHTEN","INVERTCOLOR"],
    "Debug":    ["PRINT","LOG","DEBUGON","DEBUGOFF","ASSERT","DUMPVARS","DUMPSPRITES",
                 "BENCHMARK","WATCH","STATSBAR"],
    "Scenes":   ["SCENE","SCENECLEAR"],
    "Misc":     ["COPY","SWAP","TOGGLE","RANDSEED","FPS","CLIPBOARD","TYPEOF","ISNUMBER","WAIT","WAITCLICK"],
}

ALL_COMMANDS = [c for cmds in COMMAND_DOCS.values() for c in cmds]

SNIPPETS = [
    ("Game Loop", """\
BG #111122
TITLE "My Game"
SET px 300
SET py 250
SET speed 4

:loop
FPS 60
CLEAR
BG #111122
DRAWCIRCLE player $px $py 24 #00ffcc
STATSBAR
IFKEY left  go_left
IFKEY right go_right
IFKEY up    go_up
IFKEY down  go_down
GOTO loop
:go_left
SUB px $speed
GOTO loop
:go_right
ADD px $speed
GOTO loop
:go_up
SUB py $speed
GOTO loop
:go_down
ADD py $speed
GOTO loop"""),

    ("Hello World", """\
BG #050510
TITLE "Hello, QUK!"
DRAWTEXT "Hello, World!" 32 #00ffcc 300 200
DRAWTEXT "Click anywhere to exit" 14 #445566 300 260
WAITCLICK"""),

    ("Rainbow BG", """\
SET hue 0
:loop
FPS 60
ADD hue 1
WRAP hue 0 360
HSV2HEX col $hue 1 1
BG $col
GOTO loop"""),

    ("Particle Fireworks", """\
BG #000000
TITLE "Click for Fireworks!"
:loop
FPS 60
GETMOUSE mx my
IFCLICKED 0 0 800 600 bang
GOTO loop
:bang
BURST fx $mx $my 50 #ff6600 6 6 0.2 0.97
BURST fx2 $mx $my 25 #ffff00 3 9 0.1 0.98
EXPLOSION boom $mx $my #ff4400 3
SOUND 440 80
GOTO loop"""),

    ("Bouncing Ball", """\
BG #050505
TITLE "Bouncing Ball"
DRAWCIRCLE ball 350 225 20 #ff4488
SETVEL ball 4 3
:loop
FPS 60
CLEAR
BG #050505
APPLYVELONE ball
GETPOS ball bx by
GETVEL ball vx vy
IFLT $bx 20
NEG vx
SETVEL ball $vx $vy
IFGT $bx 680
NEG vx
SETVEL ball $vx $vy
IFLT $by 20
NEG vy
SETVEL ball $vx $vy
IFGT $by 430
NEG vy
SETVEL ball $vx $vy
DRAWCIRCLE ball $bx $by 20 #ff4488
GOTO loop"""),

    ("Sprite Physics", """\
BG #0a0a20
TITLE "Physics Demo"
DRAWRECT box 300 50 40 40 #44aaff #2266cc
:loop
FPS 60
CLEAR
BG #0a0a20
APPLYGRAV 0.5
APPLYDRAG 0.995
APPLYVELONE box
GETPOS box bx by
BOUNDRECT box 0 0 760 440 hit
IFEQ $hit 1
GETVEL box vx vy
MULT vy -0.7
SETVEL box $vx $vy
DRAWRECT box $bx $by 40 40 #44aaff
GOTO loop"""),

    ("Tween & Ease", """\
BG #0a0a1a
TITLE "Tween Demo"
SET px 50
TWEEN slide px 50 650 2.0 bounce
DRAWCIRCLE ball $px 250 24 #a78bfa
:loop
FPS 60
CLEAR
BG #0a0a1a
DRAWCIRCLE ball $px 250 24 #a78bfa
DRAWTEXT "Bouncing tween!" 16 #445566 350 200
GOTO loop"""),

    ("Image Sprite", """\
// Place a PNG in same folder, e.g. hero.png
BG #111111
TITLE "Image Sprite"
DRAWIMAGE hero "hero.png" 100 100 64 64
:loop
FPS 60
IFKEY right move_r
IFKEY left  move_l
IFKEY up    move_u
IFKEY down  move_d
GOTO loop
:move_r
MOVE hero 3 0
GOTO loop
:move_l
MOVE hero -3 0
GOTO loop
:move_u
MOVE hero 0 -3
GOTO loop
:move_d
MOVE hero 0 3
GOTO loop"""),

    ("Timer & Repeat", """\
BG #111133
TITLE "Timer Demo"
SET score 0
TIMERPEAT ticker 1 add_score

:loop
FPS 60
CLEAR
BG #111133
FORMAT msg "Score: $score"
DRAWTEXT $msg 28 #fbbf24 300 200
GOTO loop

:add_score
INC score
GOTO loop"""),

    ("Scene System", """\
BG #000011
:menu
CLEAR
BG #000011
DRAWTEXT "MAIN MENU" 28 #7c3aed 300 150
DRAWTEXT "Click to Play" 16 #445566 300 220
WAITCLICK
SCENE game

:game
DRAWTEXT "GAME SCENE" 28 #22c55e 300 200
DRAWTEXT "Click to return" 14 #445566 300 260
WAITCLICK
SCENE menu"""),

    ("Dict & JSON", """\
BG #0a0a15
TITLE "Dict Demo"
DICTNEW player
DICTSET player "name" "Hero"
DICTSET player "hp" 100
DICTSET player "gold" 500

DICTGET name player "name"
DICTGET hp player "hp"
FORMAT info "Name: $name  HP: $hp"
DRAWTEXT $info 16 #00ffcc 300 200
WAITCLICK"""),

    ("Camera Follow", """\
BG #1a1a2e
TITLE "Camera Follow"
DRAWRECT hero 350 250 32 32 #f97316
SET speed 4

:loop
FPS 60
CLEAR
BG #1a1a2e
CAMFOLLOW hero 0.08
IFKEY left  ml
IFKEY right mr
IFKEY up    mu
IFKEY down  md
DRAWRECT hero 350 250 32 32 #f97316
STATSBAR
GOTO loop
:ml
MOVE hero -$speed 0
GOTO loop
:mr
MOVE hero $speed 0
GOTO loop
:mu
MOVE hero 0 -$speed
GOTO loop
:md
MOVE hero 0 $speed
GOTO loop"""),
]

DEFAULT_SCRIPT = """\
// QUK Studio v9.0 — All-in-One IDE + Engine
// ─────────────────────────────────────────
// Press F5 to run  •  Ctrl+/ to comment
// Double-click a snippet in the left panel
// to load it into the editor

BG #0a0a1a
TITLE "Welcome to QUK Studio v9"

TWEEN glow px 80 620 3.0 easeinout
TWEENLOOP pulse py 200 230 1.5 easeinout

:loop
FPS 60
CLEAR
BG #0a0a1a

// Animated title
DRAWTEXT "QUK STUDIO" 36 #7c3aed $px 140
DRAWTEXT "v9.0  •  Double-click a snippet to start" 13 #2a2a4a 350 $py

// FPS counter
STATSBAR
GOTO loop
"""

RECENT_FILE = os.path.join(os.path.expanduser("~"), ".quk_recent_v9.json")

def _load_recent():
    try:
        with open(RECENT_FILE) as f: return json.load(f)
    except: return []

def _save_recent(paths):
    try:
        with open(RECENT_FILE,"w") as f: json.dump(paths[:15],f)
    except: pass


# ═════════════════════════════════════════════════════════════════════════════
#  QUK STUDIO v9  —  Unity-like IDE
# ═════════════════════════════════════════════════════════════════════════════
class QukStudio:
    BG    = "#0e0e1a"; PANEL = "#0b0b14"; TOOL  = "#121220"; EDIT  = "#090912"
    CONS  = "#070710"; TEXT  = "#c8c8e8"; DIM   = "#303050"; DIM2  = "#505075"
    GREEN = "#22c55e"; RED   = "#ef4444"; BLUE  = "#60a5fa"; PURP  = "#a78bfa"
    AMB   = "#fbbf24"; TEAL  = "#2dd4bf"; BDR   = "#1a1a2e"; SEL   = "#1e1e3c"
    HOV   = "#161628"; ORANGE= "#fb923c"

    SYN = dict(command="#60a5fa", label="#fbbf24", comment="#252545",
               string="#34d399",  variable="#fcd34d", number="#f87171",
               hexcol="#c084fc",  curline="#13132a",  findhl="#4a3a00")

    def __init__(self):
        self.root = tk.Tk()
        self.root.title("QUK Studio v9")
        self.root.geometry("1500x900")
        self.root.minsize(1100, 650)
        self.root.configure(bg=self.BG)

        self.current_file  = None
        self.modified      = False
        self.proc          = None
        self.recent        = _load_recent()
        self.assets        = []
        self.assets_dir    = None
        self.active_tab    = "snippets"  # snippets | assets | docs
        self._var_watch    = {}          # name -> last_value string
        self._autocomplete_popup = None

        ttk.Style().theme_use("default")

        self._build_layout()
        self._setup_syntax()
        self._bind_keys()
        self._update_title()
        self._load_content(DEFAULT_SCRIPT)
        self.root.mainloop()

    # ─────────────────────────────────────────────────────────────────────
    # LAYOUT
    # ─────────────────────────────────────────────────────────────────────
    def _build_layout(self):
        self._build_toolbar()
        main = tk.PanedWindow(self.root, orient="horizontal",
            bg=self.BG, sashwidth=4, sashrelief="flat", bd=0)
        main.pack(fill="both", expand=True)

        self._build_left_panel(main)

        centre = tk.PanedWindow(main, orient="vertical",
            bg=self.BG, sashwidth=4, sashrelief="flat", bd=0)
        main.add(centre, minsize=520, width=820)
        self._build_editor(centre)
        self._build_console(centre)

        self._build_right_panel(main)

    # ─────────────────────────────────────────────────────────────────────
    # TOOLBAR
    # ─────────────────────────────────────────────────────────────────────
    def _build_toolbar(self):
        tb = tk.Frame(self.root, bg=self.TOOL, height=48)
        tb.pack(fill="x"); tb.pack_propagate(False)

        tk.Label(tb, text="⬡ QUK STUDIO", fg=self.PURP, bg=self.TOOL,
            font=("Consolas",13,"bold")).pack(side="left", padx=(14,6))
        tk.Label(tb, text="v9", fg=self.TEAL, bg=self.TOOL,
            font=("Consolas",10)).pack(side="left", padx=(0,22))

        def btn(text, cmd, bg=None, fg=None, bold=False):
            b = tk.Button(tb, text=text, command=cmd,
                bg=bg or self.TOOL, fg=fg or self.TEXT,
                font=("Consolas",9,"bold" if bold else "normal"),
                relief="flat", activebackground=self.HOV,
                activeforeground="#e0e0ff", cursor="hand2", padx=9, pady=5)
            b.pack(side="left", padx=2)
            return b

        btn("New",     self.new_file)
        btn("Open",    self.open_file)
        btn("Save",    self.save_file)
        btn("Save As", self.save_as)
        btn("Build…",  self._show_build_dialog)

        tk.Frame(tb, bg=self.BDR, width=1).pack(side="left",fill="y",padx=10,pady=6)

        self.run_btn  = btn("▶  Run  F5",  self.run_script,  bg="#166534", fg="#fff", bold=True)
        self.stop_btn = btn("■  Stop  F6", self.stop_script, bg="#7f1d1d", fg="#fff", bold=True)
        self.stop_btn.config(state="disabled")

        tk.Frame(tb, bg=self.BDR, width=1).pack(side="left",fill="y",padx=10,pady=6)

        tk.Label(tb, text="Find:", fg=self.DIM2, bg=self.TOOL,
            font=("Consolas",9)).pack(side="left")
        self.find_var = tk.StringVar()
        fe = tk.Entry(tb, textvariable=self.find_var, bg="#18182e", fg=self.TEXT,
            insertbackground=self.TEXT, relief="flat", font=("Consolas",10),
            width=20, highlightthickness=0)
        fe.pack(side="left", padx=(4,2), ipady=3)
        fe.bind("<Return>",  lambda e: self._find_next())
        fe.bind("<Shift-Return>", lambda e: self._find_prev())

        tk.Button(tb, text="↓", bg=self.TOOL, fg=self.DIM2,
            font=("Consolas",9), relief="flat", cursor="hand2",
            activebackground=self.HOV, command=self._find_next, padx=4).pack(side="left")
        tk.Button(tb, text="↑", bg=self.TOOL, fg=self.DIM2,
            font=("Consolas",9), relief="flat", cursor="hand2",
            activebackground=self.HOV, command=self._find_prev, padx=4).pack(side="left")

        self.sr = tk.Label(tb, text="Ln 1, Col 1", fg=self.DIM2, bg=self.TOOL, font=("Consolas",8))
        self.sr.pack(side="right", padx=10)
        self.sl = tk.Label(tb, text="Ready", fg=self.DIM2, bg=self.TOOL, font=("Consolas",8))
        self.sl.pack(side="right", padx=6)
        self.fname_lbl = tk.Label(tb, text="untitled.quk", fg=self.DIM, bg=self.TOOL, font=("Consolas",8))
        self.fname_lbl.pack(side="right", padx=16)

    # ─────────────────────────────────────────────────────────────────────
    # LEFT PANEL  (tabs: Snippets | Assets | Docs)
    # ─────────────────────────────────────────────────────────────────────
    def _build_left_panel(self, main):
        left = tk.Frame(main, bg=self.PANEL)
        main.add(left, minsize=190, width=230)

        # Tab bar
        tab_bar = tk.Frame(left, bg=self.PANEL)
        tab_bar.pack(fill="x")
        self._tab_btns = {}
        for name in ("Snippets","Assets","Docs"):
            b = tk.Button(tab_bar, text=name, bg=self.PANEL, fg=self.DIM2,
                font=("Consolas",8), relief="flat", cursor="hand2", padx=10, pady=5,
                activebackground=self.HOV, activeforeground=self.TEXT,
                command=lambda n=name.lower(): self._switch_tab(n))
            b.pack(side="left", fill="x", expand=True)
            self._tab_btns[name.lower()] = b

        # Tab pages (stacked frames)
        self._tab_frames = {}

        # ── Snippets tab ─────────────────────────────────────────────
        sf = tk.Frame(left, bg=self.PANEL)
        self._tab_frames["snippets"] = sf

        tk.Label(sf, text="RECENT FILES", fg=self.DIM2, bg=self.PANEL,
            font=("Consolas",7,"bold"), anchor="w", padx=10).pack(fill="x", pady=(8,2))
        self.recent_lb = tk.Listbox(sf, bg=self.PANEL, fg=self.DIM2,
            selectbackground=self.SEL, selectforeground=self.BLUE,
            relief="flat", font=("Consolas",9), bd=0, highlightthickness=0,
            cursor="hand2", activestyle="none")
        self.recent_lb.pack(fill="x", padx=6)
        self.recent_lb.bind("<Double-Button-1>", self._open_recent)
        self._refresh_recent()

        tk.Frame(sf, bg=self.BDR, height=1).pack(fill="x", padx=6, pady=4)
        tk.Label(sf, text="SNIPPETS", fg=self.DIM2, bg=self.PANEL,
            font=("Consolas",7,"bold"), anchor="w", padx=10).pack(fill="x", pady=(2,3))

        snip_scroll = tk.Frame(sf, bg=self.PANEL)
        snip_scroll.pack(fill="both", expand=True)
        snip_canvas = tk.Canvas(snip_scroll, bg=self.PANEL, highlightthickness=0, bd=0)
        snip_vsb = tk.Scrollbar(snip_scroll, orient="vertical", command=snip_canvas.yview, width=6,
            bg=self.BG, troughcolor=self.PANEL)
        snip_vsb.pack(side="right", fill="y")
        snip_canvas.pack(fill="both", expand=True)
        snip_canvas.config(yscrollcommand=snip_vsb.set)
        snip_inner = tk.Frame(snip_canvas, bg=self.PANEL)
        snip_canvas.create_window((0,0), window=snip_inner, anchor="nw")
        snip_inner.bind("<Configure>", lambda e: snip_canvas.config(scrollregion=snip_canvas.bbox("all")))

        for name, code in SNIPPETS:
            b = tk.Button(snip_inner, text=f"  {name}", anchor="w",
                bg=self.PANEL, fg=self.DIM2, relief="flat", font=("Consolas",9),
                bd=0, activebackground=self.HOV, activeforeground=self.TEXT,
                cursor="hand2", padx=6, pady=3,
                command=lambda c=code: self._insert_snippet(c))
            b.pack(fill="x", padx=4)

        # ── Assets tab ───────────────────────────────────────────────
        af = tk.Frame(left, bg=self.PANEL)
        self._tab_frames["assets"] = af

        ah = tk.Frame(af, bg=self.PANEL)
        ah.pack(fill="x", pady=(8,2))
        tk.Label(ah, text="ASSETS", fg=self.DIM2, bg=self.PANEL,
            font=("Consolas",7,"bold"), anchor="w", padx=10).pack(side="left")
        tk.Button(ah, text="+ Import", bg=self.PANEL, fg=self.TEAL,
            font=("Consolas",8), relief="flat", cursor="hand2",
            activebackground=self.HOV, bd=0, padx=4,
            command=self._import_assets).pack(side="right", padx=4)

        self.asset_dir_lbl = tk.Label(af, text="No folder set",
            fg=self.DIM, bg=self.PANEL, font=("Consolas",7), anchor="w", padx=10)
        self.asset_dir_lbl.pack(fill="x")

        asset_frame = tk.Frame(af, bg=self.PANEL)
        asset_frame.pack(fill="both", expand=True, padx=4)
        self.asset_lb = tk.Listbox(asset_frame, bg=self.PANEL, fg=self.TEAL,
            selectbackground=self.SEL, selectforeground="#ffffff",
            relief="flat", font=("Consolas",9), bd=0, highlightthickness=0,
            cursor="hand2", activestyle="none")
        asset_vsb = tk.Scrollbar(asset_frame, orient="vertical", command=self.asset_lb.yview,
            width=6, bg=self.BG, troughcolor=self.PANEL)
        asset_vsb.pack(side="right", fill="y")
        self.asset_lb.pack(fill="both", expand=True)
        self.asset_lb.config(yscrollcommand=asset_vsb.set)
        self.asset_lb.bind("<Double-Button-1>", self._insert_asset_path)
        self.asset_lb.bind("<Button-3>", self._asset_right_click)

        tk.Button(af, text="Set Folder…", bg=self.PANEL, fg=self.DIM2,
            font=("Consolas",8), relief="flat", cursor="hand2",
            activebackground=self.HOV, activeforeground=self.TEXT,
            command=self._set_asset_folder).pack(fill="x", padx=6, pady=(2,6))

        # ── Docs tab ─────────────────────────────────────────────────
        df = tk.Frame(left, bg=self.PANEL)
        self._tab_frames["docs"] = df

        tk.Label(df, text="COMMAND REFERENCE", fg=self.DIM2, bg=self.PANEL,
            font=("Consolas",7,"bold"), anchor="w", padx=10).pack(fill="x", pady=(8,3))

        doc_search_var = tk.StringVar()
        tk.Entry(df, textvariable=doc_search_var, bg="#14142a", fg=self.TEXT,
            insertbackground=self.TEXT, relief="flat", font=("Consolas",9),
            highlightthickness=0).pack(fill="x", padx=6, pady=(0,4), ipady=2)

        doc_frame = tk.Frame(df, bg=self.PANEL)
        doc_frame.pack(fill="both", expand=True, padx=4)
        doc_vsb = tk.Scrollbar(doc_frame, orient="vertical", width=6,
            bg=self.BG, troughcolor=self.PANEL)
        doc_vsb.pack(side="right", fill="y")
        self.doc_text = tk.Text(doc_frame, bg=self.PANEL, fg=self.DIM2,
            font=("Consolas",8), relief="flat", bd=0, highlightthickness=0,
            state="disabled", wrap="word", padx=4, pady=4,
            yscrollcommand=doc_vsb.set)
        doc_vsb.config(command=self.doc_text.yview)
        self.doc_text.pack(fill="both", expand=True)
        self.doc_text.tag_configure("cat",  foreground=self.AMB, font=("Consolas",8,"bold"))
        self.doc_text.tag_configure("cmd",  foreground=self.BLUE)
        self.doc_text.tag_configure("ins",  foreground=self.TEAL, font=("Consolas",8,"underline"))

        def _populate_docs(filter_text=""):
            self.doc_text.config(state="normal")
            self.doc_text.delete("1.0","end")
            ft = filter_text.upper()
            for cat, cmds in COMMAND_DOCS.items():
                visible = [c for c in cmds if ft in c] if ft else cmds
                if not visible: continue
                self.doc_text.insert("end", f"\n{cat}\n", "cat")
                for i,c in enumerate(visible):
                    tag = f"ins_{c}"
                    self.doc_text.insert("end", f"  {c}", ("cmd", tag))
                    self.doc_text.insert("end", "  " if i<len(visible)-1 else "")
                    self.doc_text.tag_bind(tag, "<Button-1>",
                        lambda e, cmd=c: self.editor.insert(tk.INSERT, cmd+" "))
                self.doc_text.insert("end", "\n")
            self.doc_text.config(state="disabled")

        _populate_docs()
        doc_search_var.trace_add("write", lambda *a: _populate_docs(doc_search_var.get()))

        # Show initial tab
        self._switch_tab("snippets")

    def _switch_tab(self, name):
        for n, f in self._tab_frames.items():
            f.pack_forget()
        self._tab_frames[name].pack(fill="both", expand=True)
        for n, b in self._tab_btns.items():
            b.config(bg=self.SEL if n==name else self.PANEL,
                     fg=self.TEXT if n==name else self.DIM2)
        self.active_tab = name

    # ─────────────────────────────────────────────────────────────────────
    # EDITOR
    # ─────────────────────────────────────────────────────────────────────
    def _build_editor(self, parent):
        ef = tk.Frame(parent, bg=self.EDIT)
        parent.add(ef, minsize=200)

        # minimap (thin strip on far right)
        self.minimap = tk.Canvas(ef, width=60, bg="#07070e",
            highlightthickness=0, bd=0)
        self.minimap.pack(side="right", fill="y")

        erow = tk.Frame(ef, bg=self.EDIT)
        erow.pack(fill="both", expand=True)

        self.ln_widget = tk.Text(erow, width=4, bg="#0c0c1c", fg=self.DIM,
            font=("Consolas",12), state="disabled", relief="flat",
            bd=0, highlightthickness=0, padx=6, pady=5,
            cursor="arrow", selectbackground="#0c0c1c")
        self.ln_widget.pack(side="left", fill="y")

        self.vsb = tk.Scrollbar(erow, orient="vertical", width=8,
            bg=self.BG, troughcolor=self.PANEL, activebackground=self.DIM)
        self.vsb.pack(side="right", fill="y")

        hsb = tk.Scrollbar(ef, orient="horizontal",
            bg=self.BG, troughcolor=self.PANEL)
        hsb.pack(side="bottom", fill="x")

        self.editor = tk.Text(erow, bg=self.EDIT, fg=self.TEXT,
            insertbackground=self.PURP, font=("Consolas",12),
            relief="flat", bd=0, highlightthickness=0,
            padx=14, pady=5, undo=True, wrap="none",
            yscrollcommand=self._on_vscroll,
            xscrollcommand=hsb.set,
            selectbackground="#252548", selectforeground=self.TEXT,
            tabs="4c", spacing1=2, spacing3=2)
        self.editor.pack(side="left", fill="both", expand=True)
        self.vsb.config(command=self._scroll_both)
        hsb.config(command=self.editor.xview)

    # ─────────────────────────────────────────────────────────────────────
    # CONSOLE
    # ─────────────────────────────────────────────────────────────────────
    def _build_console(self, parent):
        cf = tk.Frame(parent, bg=self.CONS)
        parent.add(cf, minsize=80, height=180)

        ch = tk.Frame(cf, bg="#0a0a18")
        ch.pack(fill="x")
        tk.Label(ch, text="OUTPUT", fg=self.DIM, bg="#0a0a18",
            font=("Consolas",7,"bold")).pack(side="left", padx=10, pady=4)
        tk.Button(ch, text="Clear", bg="#0a0a18", fg=self.DIM,
            font=("Consolas",8), relief="flat", cursor="hand2",
            activebackground=self.HOV, command=self._clear_console).pack(side="right", padx=8)
        tk.Button(ch, text="Copy All", bg="#0a0a18", fg=self.DIM,
            font=("Consolas",8), relief="flat", cursor="hand2",
            activebackground=self.HOV, command=self._copy_console).pack(side="right", padx=4)

        con_row = tk.Frame(cf, bg=self.CONS)
        con_row.pack(fill="both", expand=True)
        self.console = tk.Text(con_row, bg=self.CONS, fg="#86efac",
            font=("Consolas",10), relief="flat", bd=0,
            highlightthickness=0, padx=10, pady=5,
            state="disabled", wrap="word", selectbackground="#1a2a1a")
        self.console.pack(side="left", fill="both", expand=True)
        cvsb = tk.Scrollbar(con_row, orient="vertical", width=6,
            bg=self.BG, troughcolor=self.PANEL)
        cvsb.pack(side="right", fill="y")
        self.console.config(yscrollcommand=cvsb.set)
        cvsb.config(command=self.console.yview)

    # ─────────────────────────────────────────────────────────────────────
    # RIGHT PANEL  (Inspector + Var Watch + Build Info)
    # ─────────────────────────────────────────────────────────────────────
    def _build_right_panel(self, main):
        right = tk.Frame(main, bg=self.PANEL)
        main.add(right, minsize=210, width=260)

        r_canvas = tk.Canvas(right, bg=self.PANEL, highlightthickness=0, bd=0)
        r_vsb = tk.Scrollbar(right, orient="vertical", command=r_canvas.yview,
            width=6, bg=self.BG, troughcolor=self.PANEL)
        r_vsb.pack(side="right", fill="y")
        r_canvas.pack(fill="both", expand=True)
        r_canvas.config(yscrollcommand=r_vsb.set)
        inner = tk.Frame(r_canvas, bg=self.PANEL)
        r_canvas.create_window((0,0), window=inner, anchor="nw")
        inner.bind("<Configure>", lambda e: r_canvas.config(scrollregion=r_canvas.bbox("all")))

        def sec(text):
            tk.Frame(inner, bg=self.BDR, height=1).pack(fill="x", padx=6, pady=(6,0))
            tk.Label(inner, text=text, fg=self.DIM2, bg=self.PANEL,
                font=("Consolas",7,"bold"), anchor="w", padx=10).pack(fill="x", pady=(4,3))

        def row_entry(label, var, width=14):
            r = tk.Frame(inner, bg=self.PANEL)
            r.pack(fill="x", padx=8, pady=1)
            tk.Label(r, text=label+":", fg=self.DIM2, bg=self.PANEL,
                font=("Consolas",8), width=6, anchor="w").pack(side="left")
            e = tk.Entry(r, textvariable=var, bg="#14142a", fg=self.TEXT,
                insertbackground=self.TEXT, relief="flat",
                font=("Consolas",9), width=width, highlightthickness=0)
            e.pack(side="left", fill="x", expand=True, ipady=2)
            return e

        # ── SPRITE INSPECTOR ─────────────────────────────────────────
        sec("SPRITE INSPECTOR")
        self.sprite_id_var = tk.StringVar()
        row_entry("ID", self.sprite_id_var)

        self._sprop = {}
        for prop, label in [("x","X"),("y","Y"),("w","W"),("h","H"),("vx","Vx"),("vy","Vy"),("angle","Ang")]:
            r = tk.Frame(inner, bg=self.PANEL)
            r.pack(fill="x", padx=8, pady=1)
            tk.Label(r, text=f"{label}:", fg=self.DIM2, bg=self.PANEL,
                font=("Consolas",8), width=5, anchor="w").pack(side="left")
            var = tk.StringVar(value="—")
            tk.Label(r, textvariable=var, fg=self.TEAL, bg=self.PANEL,
                font=("Consolas",9), anchor="w").pack(side="left")
            self._sprop[prop] = var

        # Quick sprite insert buttons
        sec("SPRITE ACTIONS")
        sprite_actions = [
            ("MOVE →",   "MOVE {id} 4 0"),    ("MOVE ↓",   "MOVE {id} 0 4"),
            ("SETVEL",   "SETVEL {id} 3 -8"), ("HIDE",     "HIDE {id}"),
            ("SHOW",     "SHOW {id}"),         ("DELETE",   "DELETE {id}"),
            ("COLLIDE",  "COLLIDE {id} other hit"),
            ("TWEEN X",  "TWEEN tw1 px 0 400 2.0 bounce"),
            ("BURST",    "BURST fx {x} {y} 30 #ff6600 5 4 0.2"),
            ("MOVETOWARD","MOVETOWARD {id} $mouse_x $mouse_y 3"),
        ]
        for lbl, tmpl in sprite_actions:
            def make_cmd(t=tmpl):
                sid = self.sprite_id_var.get() or "id"
                line = t.replace("{id}", sid).replace("{x}","300").replace("{y}","300")
                self.editor.insert(tk.INSERT, line+"\n")
            tk.Button(inner, text=lbl, bg=self.HOV, fg=self.TEXT,
                font=("Consolas",8), relief="flat", anchor="w",
                cursor="hand2", activebackground=self.SEL,
                activeforeground="#fff", padx=10, pady=2,
                command=make_cmd).pack(fill="x", padx=6, pady=1)

        # ── PARTICLE CONTROLS ────────────────────────────────────────
        sec("PARTICLE CONTROLS")
        self.particle_id_var = tk.StringVar(value="fx")
        row_entry("ID", self.particle_id_var)

        self._p = {}
        sliders = [("Count","count",1,200,40),("Speed","speed",1,20,5),
                   ("Gravity","grav",0,20,2),("Size","size",1,20,4),
                   ("Drag%","drag",80,100,97)]
        for lbl,key,lo,hi,default in sliders:
            r = tk.Frame(inner, bg=self.PANEL); r.pack(fill="x", padx=8, pady=1)
            tk.Label(r, text=f"{lbl}:", fg=self.DIM2, bg=self.PANEL,
                font=("Consolas",7), width=7, anchor="w").pack(side="left")
            var = tk.DoubleVar(value=default)
            tk.Scale(r, from_=lo, to=hi, orient="horizontal", variable=var,
                bg=self.PANEL, fg=self.DIM2, troughcolor=self.SEL,
                highlightthickness=0, bd=0, showvalue=False,
                sliderrelief="flat", sliderlength=10, length=90).pack(side="left")
            tk.Label(r, textvariable=var, fg=self.TEAL, bg=self.PANEL,
                font=("Consolas",7), width=4).pack(side="left")
            self._p[key] = var

        def _insert_particle(style):
            pid   = self.particle_id_var.get() or "fx"
            count = int(self._p["count"].get())
            speed = round(self._p["speed"].get(),1)
            grav  = round(self._p["grav"].get()*0.1,2)
            size  = int(self._p["size"].get())
            drag  = round(self._p["drag"].get()/100,3)
            if style=="burst":
                self.editor.insert(tk.INSERT,
                    f"BURST {pid} $mouse_x $mouse_y {count} #ff6600 {size} {speed} {grav} {drag}\n")
            elif style=="stream":
                self.editor.insert(tk.INSERT,
                    f"STREAM {pid} 300 0 270 #44aaff {count} {drag}\n")
            elif style=="explosion":
                self.editor.insert(tk.INSERT,
                    f"EXPLOSION {pid} $mouse_x $mouse_y #ff4400 3\n")
            elif style=="clear":
                self.editor.insert(tk.INSERT, f"CLEARPARTICLES {pid}\n")

        for lbl, style in [("BURST","burst"),("STREAM","stream"),("EXPLOSION","explosion"),("CLEAR","clear")]:
            tk.Button(inner, text=f"Insert {lbl}", bg=self.HOV, fg=self.TEAL,
                font=("Consolas",8), relief="flat", cursor="hand2",
                activebackground=self.SEL, activeforeground="#fff",
                padx=10, pady=2,
                command=lambda s=style: _insert_particle(s)).pack(fill="x", padx=6, pady=1)

        # ── TWEEN BUILDER ────────────────────────────────────────────
        sec("TWEEN BUILDER")
        tween_fields = {}
        for lbl,key,default in [("Var","var","px"),("From","frm","0"),("To","to","400"),
                                  ("Dur(s)","dur","1.5"),("Ease","ease","easeinout")]:
            r = tk.Frame(inner, bg=self.PANEL); r.pack(fill="x", padx=8, pady=1)
            tk.Label(r, text=f"{lbl}:", fg=self.DIM2, bg=self.PANEL,
                font=("Consolas",8), width=7, anchor="w").pack(side="left")
            var = tk.StringVar(value=default)
            tk.Entry(r, textvariable=var, bg="#14142a", fg=self.TEXT,
                insertbackground=self.TEXT, relief="flat",
                font=("Consolas",9), width=8, highlightthickness=0).pack(side="left", ipady=2)
            tween_fields[key] = var

        ease_choices = ["linear","easein","easeout","easeinout","bounce","spring","elastic"]
        ease_menu = tk.OptionMenu(inner, tween_fields["ease"], *ease_choices)
        ease_menu.config(bg=self.HOV, fg=self.TEXT, activebackground=self.SEL,
            font=("Consolas",8), relief="flat", bd=0, highlightthickness=0)
        ease_menu.pack(fill="x", padx=8, pady=2)

        def insert_tween():
            v=tween_fields["var"].get(); f=tween_fields["frm"].get()
            t=tween_fields["to"].get(); d=tween_fields["dur"].get()
            e=tween_fields["ease"].get()
            self.editor.insert(tk.INSERT, f"TWEEN tw1 {v} {f} {t} {d} {e}\n")

        def insert_tweenloop():
            v=tween_fields["var"].get(); f=tween_fields["frm"].get()
            t=tween_fields["to"].get(); d=tween_fields["dur"].get()
            e=tween_fields["ease"].get()
            self.editor.insert(tk.INSERT, f"TWEENLOOP tw1 {v} {f} {t} {d} {e}\n")

        for lbl, cmd in [("Insert TWEEN", insert_tween), ("Insert TWEENLOOP", insert_tweenloop)]:
            tk.Button(inner, text=lbl, bg=self.HOV, fg=self.PURP,
                font=("Consolas",8), relief="flat", cursor="hand2",
                activebackground=self.SEL, padx=10, pady=2,
                command=cmd).pack(fill="x", padx=6, pady=1)

        # ── VAR WATCH ────────────────────────────────────────────────
        sec("VAR WATCH")
        watch_entry_var = tk.StringVar()
        wr = tk.Frame(inner, bg=self.PANEL); wr.pack(fill="x", padx=8, pady=2)
        tk.Entry(wr, textvariable=watch_entry_var, bg="#14142a", fg=self.TEXT,
            insertbackground=self.TEXT, relief="flat", font=("Consolas",9),
            width=12, highlightthickness=0).pack(side="left", ipady=2, fill="x", expand=True)
        tk.Button(wr, text="+", bg=self.PANEL, fg=self.TEAL,
            font=("Consolas",10,"bold"), relief="flat", cursor="hand2",
            activebackground=self.HOV, bd=0, padx=4,
            command=lambda: self._add_watch(watch_entry_var.get())).pack(side="left")

        self.watch_frame = tk.Frame(inner, bg=self.PANEL)
        self.watch_frame.pack(fill="x", padx=8)
        self.watch_labels = {}

        # ── BUILD INFO ───────────────────────────────────────────────
        sec("BUILD / PYINSTALLER")
        build_info = [
            "pyinstaller --onefile",
            "  --windowed",
            "  --name QUK_Studio",
            "  --add-data assets;assets",
            "  --add-data themes;themes",
            "  --hidden-import PIL",
            "  --hidden-import PIL.ImageTk",
            "  quk_studio.py",
        ]
        for line in build_info:
            tk.Label(inner, text=line, fg=self.DIM2, bg=self.PANEL,
                font=("Consolas",7), anchor="w", padx=10).pack(fill="x")
        tk.Button(inner, text="Generate build.bat", bg=self.HOV, fg=self.AMB,
            font=("Consolas",8), relief="flat", cursor="hand2",
            activebackground=self.SEL, padx=10, pady=2,
            command=self._gen_build_bat).pack(fill="x", padx=6, pady=4)
        tk.Button(inner, text="Generate build.sh", bg=self.HOV, fg=self.TEAL,
            font=("Consolas",8), relief="flat", cursor="hand2",
            activebackground=self.SEL, padx=10, pady=2,
            command=self._gen_build_sh).pack(fill="x", padx=6, pady=2)

    # ─────────────────────────────────────────────────────────────────────
    # SYNTAX
    # ─────────────────────────────────────────────────────────────────────
    def _setup_syntax(self):
        e = self.editor
        for tag, cfg in self.SYN.items():
            if tag == "curline": e.tag_configure(tag, background=cfg)
            elif tag == "findhl": e.tag_configure(tag, background=cfg, foreground="#fde68a")
            else: e.tag_configure(tag, foreground=cfg)

    # ─────────────────────────────────────────────────────────────────────
    # KEY BINDINGS
    # ─────────────────────────────────────────────────────────────────────
    def _bind_keys(self):
        self.editor.bind("<<Modified>>",       self._on_modified)
        self.editor.bind("<KeyRelease>",       self._on_key_release)
        self.editor.bind("<ButtonRelease-1>",  self._update_cursor)
        self.editor.bind("<Tab>",              self._do_tab)
        self.editor.bind("<Control-slash>",    self._toggle_comment)
        self.editor.bind("<Control-d>",        self._duplicate_line)
        self.editor.bind("<space>",            self._on_space)
        self.root.bind("<Control-s>",   lambda e: self.save_file())
        self.root.bind("<Control-S>",   lambda e: self.save_as())
        self.root.bind("<Control-n>",   lambda e: self.new_file())
        self.root.bind("<Control-o>",   lambda e: self.open_file())
        self.root.bind("<F5>",          lambda e: self.run_script())
        self.root.bind("<F6>",          lambda e: self.stop_script())
        self.root.bind("<F1>",          lambda e: self._switch_tab("docs"))
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    def _do_tab(self, e):
        self.editor.insert(tk.INSERT, "    "); return "break"

    def _duplicate_line(self, e):
        pos = self.editor.index(tk.INSERT)
        line_start = self.editor.index("insert linestart")
        line_end   = self.editor.index("insert lineend")
        text = self.editor.get(line_start, line_end)
        self.editor.insert(line_end, "\n" + text)
        return "break"

    def _on_space(self, e):
        # Autocomplete: if the current token is an exact command, show docs hint
        pass

    def _toggle_comment(self, e):
        try:   s, en = self.editor.index("sel.first linestart"), self.editor.index("sel.last lineend")
        except: s = en = self.editor.index("insert linestart")
        lines = self.editor.get(s, en).splitlines(True)
        all_c = all(l.lstrip().startswith("//") for l in lines if l.strip())
        out = []
        for l in lines:
            if all_c: out.append(re.sub(r'^(\s*)// ?', r'\1', l))
            else:
                ind = l[:len(l)-len(l.lstrip())]; out.append(ind + "// " + l.lstrip())
        self.editor.delete(s, en)
        self.editor.insert(s, "".join(out).rstrip("\n"))
        return "break"

    # ─────────────────────────────────────────────────────────────────────
    # SCROLL SYNC + EDITOR EVENTS
    # ─────────────────────────────────────────────────────────────────────
    def _on_vscroll(self, first, last):
        self.vsb.set(first, last)
        self.ln_widget.yview_moveto(float(first))
        self._update_minimap()

    def _scroll_both(self, *args):
        self.editor.yview(*args)
        self.ln_widget.yview(*args)

    def _on_modified(self, e):
        if self.editor.edit_modified():
            self.modified = True; self._update_title()
            self.editor.edit_modified(False)

    def _on_key_release(self, e):
        self._update_line_nums()
        self._highlight_cur_line()
        self._highlight_syntax()
        self._update_cursor()

    def _update_cursor(self, e=None):
        pos = self.editor.index(tk.INSERT)
        ln, col = pos.split(".")
        self.sr.config(text=f"Ln {ln}, Col {int(col)+1}")

    def _update_line_nums(self):
        content = self.editor.get("1.0","end-1c")
        n = content.count("\n") + 1
        self.ln_widget.config(state="normal")
        self.ln_widget.delete("1.0","end")
        self.ln_widget.insert("1.0", "\n".join(str(i) for i in range(1,n+1)))
        self.ln_widget.config(state="disabled", width=max(3,len(str(n)))+1)

    def _highlight_cur_line(self):
        self.editor.tag_remove("curline","1.0","end")
        self.editor.tag_add("curline","insert linestart","insert lineend+1c")

    def _highlight_syntax(self):
        e = self.editor
        for tag in ("command","label","comment","string","variable","number","hexcol"):
            e.tag_remove(tag,"1.0","end")
        content = e.get("1.0","end")
        for ln_i, line in enumerate(content.split("\n"), 1):
            stripped = line.lstrip()
            if stripped.startswith("//") or stripped.startswith("#"):
                e.tag_add("comment",f"{ln_i}.0",f"{ln_i}.end"); continue
            if stripped.startswith(":"):
                e.tag_add("label",f"{ln_i}.0",f"{ln_i}.end"); continue
            cmt = re.search(r'(?<!:)//.*$', line)
            if cmt: e.tag_add("comment",f"{ln_i}.{cmt.start()}",f"{ln_i}.end")
            for m in re.finditer(r'"[^"]*"', line):
                e.tag_add("string",f"{ln_i}.{m.start()}",f"{ln_i}.{m.end()}")
            for m in re.finditer(r'#[0-9a-fA-F]{3,6}\b', line):
                e.tag_add("hexcol",f"{ln_i}.{m.start()}",f"{ln_i}.{m.end()}")
            for m in re.finditer(r'\$[\w]+(?:\[\d+\])?', line):
                e.tag_add("variable",f"{ln_i}.{m.start()}",f"{ln_i}.{m.end()}")
            for m in re.finditer(r'\b\d+\.?\d*\b', line):
                e.tag_add("number",f"{ln_i}.{m.start()}",f"{ln_i}.{m.end()}")
            ft = re.match(r'\s*(\w+)', line)
            if ft and ft.group(1).upper() in ALL_COMMANDS:
                e.tag_add("command",f"{ln_i}.{ft.start(1)}",f"{ln_i}.{ft.end(1)}")

    def _update_minimap(self):
        try:
            self.minimap.delete("all")
            content = self.editor.get("1.0","end-1c")
            lines   = content.split("\n")
            w, h    = 60, self.minimap.winfo_height() or 400
            if not lines: return
            lh = max(1, h / max(len(lines),1))
            for i, line in enumerate(lines):
                y = i * lh
                stripped = line.lstrip()
                if stripped.startswith("//") or stripped.startswith("#"):
                    color = self.SYN["comment"]
                elif stripped.startswith(":"):
                    color = self.SYN["label"]
                elif stripped and stripped.split()[0].upper() in ALL_COMMANDS:
                    color = self.SYN["command"]
                else:
                    color = "#1a1a30"
                bar_w = min(w, max(4, len(line) * 0.3))
                self.minimap.create_rectangle(0, y, bar_w, y+max(1,lh-0.5),
                    fill=color, outline="")
        except: pass

    # ─────────────────────────────────────────────────────────────────────
    # FILE OPS
    # ─────────────────────────────────────────────────────────────────────
    def new_file(self, e=None):
        if self.modified and not messagebox.askyesno("Unsaved","Discard unsaved changes?"): return
        self._load_content(DEFAULT_SCRIPT)
        self.current_file = None; self.modified = False; self._update_title()

    def open_file(self, e=None):
        p = filedialog.askopenfilename(title="Open QUK Script",
            filetypes=[("QUK Scripts","*.quk"),("All Files","*.*")])
        if p: self._do_open(p)

    def _do_open(self, path):
        try:
            with open(path,"r",encoding="utf-8",errors="replace") as f: txt=f.read()
            self._load_content(txt)
            self.current_file=path; self.modified=False
            self._update_title(); self._add_recent(path)
            self._log(f"Opened: {path}\n", self.BLUE)
        except Exception as ex: messagebox.showerror("Error", str(ex))

    def _load_content(self, text):
        self.editor.delete("1.0","end")
        self.editor.insert("1.0", text)
        self._update_line_nums(); self._highlight_syntax()
        self._update_minimap()

    def save_file(self, e=None):
        if self.current_file: self._do_save(self.current_file)
        else: self.save_as()

    def save_as(self, e=None):
        p = filedialog.asksaveasfilename(title="Save QUK Script",
            defaultextension=".quk",
            filetypes=[("QUK Scripts","*.quk"),("All Files","*.*")])
        if p: self._do_save(p)

    def _do_save(self, path):
        try:
            with open(path,"w",encoding="utf-8") as f:
                f.write(self.editor.get("1.0","end-1c"))
            self.current_file=path; self.modified=False
            self._update_title(); self._add_recent(path)
            self._log(f"Saved: {path}\n", self.GREEN)
        except Exception as ex: messagebox.showerror("Error", str(ex))

    def _update_title(self):
        name = os.path.basename(self.current_file) if self.current_file else "untitled.quk"
        dot  = " ●" if self.modified else ""
        self.root.title(f"QUK Studio v9 — {name}{dot}")
        self.fname_lbl.config(text=name)

    # ─────────────────────────────────────────────────────────────────────
    # RECENT
    # ─────────────────────────────────────────────────────────────────────
    def _add_recent(self, path):
        if path in self.recent: self.recent.remove(path)
        self.recent.insert(0, path); self.recent = self.recent[:15]
        _save_recent(self.recent); self._refresh_recent()

    def _refresh_recent(self):
        self.recent_lb.delete(0,"end")
        for p in self.recent: self.recent_lb.insert("end", os.path.basename(p))

    def _open_recent(self, e):
        idx = self.recent_lb.curselection()
        if idx and idx[0] < len(self.recent): self._do_open(self.recent[idx[0]])

    def _insert_snippet(self, code):
        if messagebox.askyesno("Insert Snippet","Replace editor content with this snippet?"):
            self._load_content(code)

    # ─────────────────────────────────────────────────────────────────────
    # ASSETS
    # ─────────────────────────────────────────────────────────────────────
    ASSET_EXTS = {".png","jpg",".jpeg",".gif",".bmp",".wav",".mp3",".ogg",
                  ".json",".quk",".txt",".ttf",".otf",".svg"}

    def _set_asset_folder(self):
        d = filedialog.askdirectory(title="Select Asset Folder")
        if d:
            self.assets_dir = d
            self.asset_dir_lbl.config(text=f"📁 {os.path.basename(d)}")
            self._scan_assets()

    def _scan_assets(self):
        if not self.assets_dir or not os.path.isdir(self.assets_dir): return
        ICONS = {"png":"🖼","jpg":"🖼","jpeg":"🖼","gif":"🖼","bmp":"🖼",
                 "wav":"🔊","mp3":"🔊","ogg":"🔊","ttf":"🔤","otf":"🔤",
                 "json":"📄","quk":"⬡","txt":"📄","svg":"🎨"}
        self.assets=[]; self.asset_lb.delete(0,"end")
        for f in sorted(os.listdir(self.assets_dir)):
            ext = os.path.splitext(f)[1].lower().lstrip(".")
            full = os.path.join(self.assets_dir, f)
            if os.path.isfile(full):
                icon = ICONS.get(ext,"📎")
                self.assets.append(full)
                self.asset_lb.insert("end", f"{icon} {f}")

    def _import_assets(self):
        files = filedialog.askopenfilenames(title="Import Assets")
        if not files: return
        if not self.assets_dir:
            self.assets_dir = os.path.dirname(files[0])
            self.asset_dir_lbl.config(text=f"📁 {os.path.basename(self.assets_dir)}")
        for f in files:
            dest = os.path.join(self.assets_dir, os.path.basename(f))
            if f != dest:
                try: shutil.copy2(f, dest)
                except: pass
        self._scan_assets()
        self._log(f"Imported {len(files)} asset(s)\n", self.TEAL)

    def _insert_asset_path(self, e):
        idx = self.asset_lb.curselection()
        if not idx or idx[0]>=len(self.assets): return
        path = self.assets[idx[0]]; fname = os.path.basename(path)
        ext  = os.path.splitext(fname)[1].lower()
        if ext in (".png",".jpg",".jpeg",".gif",".bmp"):
            snippet = f'DRAWIMAGE sprite "{fname}" 100 100 64 64\n'
        elif ext in (".wav",".mp3",".ogg"):
            snippet = f'// Audio: "{fname}" — use SOUND for beep, or shell player\n'
        elif ext == ".quk":
            snippet = f'// Sub-script: "{fname}"\n'
        else:
            snippet = f'"{fname}"'
        self.editor.insert(tk.INSERT, snippet); self.editor.focus_set()

    def _asset_right_click(self, e):
        idx = self.asset_lb.nearest(e.y)
        if idx<0 or idx>=len(self.assets): return
        path = self.assets[idx]
        menu = tk.Menu(self.root, tearoff=0, bg=self.PANEL, fg=self.TEXT,
            activebackground=self.SEL, font=("Consolas",9), bd=0, relief="flat")
        menu.add_command(label='Insert path', command=lambda: self.editor.insert(tk.INSERT, f'"{os.path.basename(path)}"'))
        menu.add_command(label='Open file',   command=lambda: webbrowser.open(path))
        menu.add_command(label='Delete file', command=lambda: self._delete_asset(path))
        menu.tk_popup(e.x_root, e.y_root)

    def _delete_asset(self, path):
        if messagebox.askyesno("Delete",f"Delete {os.path.basename(path)}?"):
            try: os.remove(path)
            except: pass
            self._scan_assets()

    # ─────────────────────────────────────────────────────────────────────
    # VAR WATCH
    # ─────────────────────────────────────────────────────────────────────
    def _add_watch(self, name):
        name = name.strip().lower()
        if not name or name in self.watch_labels: return
        r = tk.Frame(self.watch_frame, bg=self.PANEL); r.pack(fill="x", pady=1)
        tk.Label(r, text=f"{name}:", fg=self.DIM2, bg=self.PANEL,
            font=("Consolas",8), width=10, anchor="w").pack(side="left")
        var = tk.StringVar(value="—")
        tk.Label(r, textvariable=var, fg=self.AMB, bg=self.PANEL,
            font=("Consolas",9)).pack(side="left")
        tk.Button(r, text="✕", bg=self.PANEL, fg=self.DIM, font=("Consolas",7),
            relief="flat", cursor="hand2", bd=0,
            command=lambda n=name, row=r: self._remove_watch(n, row)).pack(side="right")
        self.watch_labels[name] = var

    def _remove_watch(self, name, row):
        row.destroy()
        self.watch_labels.pop(name, None)

    # ─────────────────────────────────────────────────────────────────────
    # FIND
    # ─────────────────────────────────────────────────────────────────────
    def _find_next(self):
        q = self.find_var.get()
        if not q: return
        self.editor.tag_remove("findhl","1.0","end")
        start = self.editor.search(q,"insert+1c",stopindex="end",nocase=True)
        if not start: start = self.editor.search(q,"1.0",stopindex="end",nocase=True)
        if start:
            end = f"{start}+{len(q)}c"
            self.editor.tag_add("findhl",start,end)
            self.editor.mark_set("insert",end); self.editor.see(start)

    def _find_prev(self):
        q = self.find_var.get()
        if not q: return
        self.editor.tag_remove("findhl","1.0","end")
        start = self.editor.search(q,"insert-1c",stopindex="1.0",nocase=True,backwards=True)
        if start:
            end = f"{start}+{len(q)}c"
            self.editor.tag_add("findhl",start,end)
            self.editor.mark_set("insert",start); self.editor.see(start)

    # ─────────────────────────────────────────────────────────────────────
    # BUILD DIALOG & SCRIPT GENERATION
    # ─────────────────────────────────────────────────────────────────────
    def _show_build_dialog(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("Build Settings")
        dlg.geometry("560x460")
        dlg.configure(bg=self.PANEL)
        dlg.grab_set()

        tk.Label(dlg, text="Build QUK Studio EXE", fg=self.PURP, bg=self.PANEL,
            font=("Consolas",13,"bold")).pack(pady=(16,6))

        fields = {}
        defaults = [
            ("App Name",   "QUK_Studio"),
            ("Icon (.ico)","quk.ico"),
            ("Extra --add-data", ""),
            ("Extra --hidden-import",""),
        ]
        for label, default in defaults:
            r = tk.Frame(dlg, bg=self.PANEL); r.pack(fill="x", padx=20, pady=3)
            tk.Label(r, text=label+":", fg=self.DIM2, bg=self.PANEL,
                font=("Consolas",9), width=22, anchor="w").pack(side="left")
            var = tk.StringVar(value=default)
            tk.Entry(r, textvariable=var, bg="#14142a", fg=self.TEXT,
                insertbackground=self.TEXT, relief="flat", font=("Consolas",10),
                highlightthickness=0).pack(side="left", fill="x", expand=True, ipady=3)
            fields[label] = var

        # Checkboxes
        opts = {}
        for opt, default in [("--onefile", True),("--windowed",True),
                              ("--add-data assets;assets",True),
                              ("--add-data themes;themes",False),
                              ("--hidden-import PIL",True),
                              ("--hidden-import PIL.ImageTk",True)]:
            var = tk.BooleanVar(value=default)
            tk.Checkbutton(dlg, text=opt, variable=var, bg=self.PANEL, fg=self.TEXT,
                selectcolor=self.SEL, activebackground=self.PANEL,
                font=("Consolas",9), anchor="w").pack(fill="x", padx=24)
            opts[opt] = var

        preview = tk.Text(dlg, bg=self.EDIT, fg=self.DIM2, font=("Consolas",8),
            height=5, relief="flat", bd=0, highlightthickness=0, padx=8, pady=4)
        preview.pack(fill="x", padx=20, pady=6)

        def _update_preview(*a):
            cmd  = ["pyinstaller"]
            name = fields["App Name"].get()
            icon = fields["Icon (.ico)"].get()
            for opt, var in opts.items():
                if var.get(): cmd.append("  " + opt)
            if name: cmd.append(f"  --name {name}")
            if icon and os.path.exists(icon): cmd.append(f"  --icon {icon}")
            extra_data = fields["Extra --add-data"].get()
            if extra_data: cmd.append(f"  --add-data {extra_data}")
            extra_hi = fields["Extra --hidden-import"].get()
            if extra_hi: cmd.append(f"  --hidden-import {extra_hi}")
            script = os.path.basename(__file__)
            cmd.append(f"  {script}")
            preview.config(state="normal"); preview.delete("1.0","end")
            preview.insert("1.0", " \\\n".join(cmd))
            preview.config(state="disabled")

        for v in list(fields.values())+list(opts.values()):
            v.trace_add("write", _update_preview)
        _update_preview()

        def _save_bat():
            script = os.path.basename(__file__)
            name = fields["App Name"].get() or "QUK_Studio"
            icon = fields["Icon (.ico)"].get()
            parts = ["pyinstaller --onefile --windowed"]
            for opt, var in opts.items():
                if var.get() and not opt.startswith("--onefile") and not opt.startswith("--windowed"):
                    parts.append(opt)
            parts.append(f"--name {name}")
            if icon and os.path.exists(icon): parts.append(f"--icon {icon}")
            extra_data = fields["Extra --add-data"].get()
            if extra_data: parts.append(f"--add-data {extra_data}")
            cmd = " ^\n  ".join(parts) + f" ^\n  {script}"
            bat = f"@echo off\n{cmd}\npause\n"
            path = filedialog.asksaveasfilename(defaultextension=".bat",
                filetypes=[("Batch Files","*.bat")])
            if path:
                with open(path,"w") as f: f.write(bat)
                self._log(f"Saved: {path}\n", self.GREEN)
            dlg.destroy()

        tk.Button(dlg, text="Save build.bat", bg="#166534", fg="#fff",
            font=("Consolas",10,"bold"), relief="flat", cursor="hand2",
            padx=16, pady=6, command=_save_bat).pack(pady=8)

    def _gen_build_bat(self):
        script = os.path.basename(__file__)
        bat = (
            "@echo off\n"
            "pyinstaller --onefile --windowed ^\n"
            "  --name QUK_Studio ^\n"
            "  --add-data \"assets;assets\" ^\n"
            "  --add-data \"themes;themes\" ^\n"
            "  --hidden-import PIL ^\n"
            "  --hidden-import PIL.ImageTk ^\n"
            f"  {script}\n"
            "pause\n"
        )
        p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "build.bat")
        with open(p,"w") as f: f.write(bat)
        self._log(f"Generated: {p}\n", self.AMB)

    def _gen_build_sh(self):
        script = os.path.basename(__file__)
        sh = (
            "#!/bin/bash\n"
            "pyinstaller --onefile --windowed \\\n"
            "  --name QUK_Studio \\\n"
            "  --add-data 'assets:assets' \\\n"
            "  --add-data 'themes:themes' \\\n"
            "  --hidden-import PIL \\\n"
            "  --hidden-import PIL.ImageTk \\\n"
            f"  {script}\n"
        )
        p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "build.sh")
        with open(p,"w") as f: f.write(sh)
        try: os.chmod(p, 0o755)
        except: pass
        self._log(f"Generated: {p}\n", self.TEAL)

    # ─────────────────────────────────────────────────────────────────────
    # RUN / STOP
    # ─────────────────────────────────────────────────────────────────────
    def run_script(self, e=None):
        if self.proc and self.proc.poll() is None:
            self._log("Already running — F6 to stop.\n", self.RED); return
        if not self.current_file:
            t = tempfile.NamedTemporaryFile(suffix=".quk",delete=False,mode="w",encoding="utf-8")
            t.write(self.editor.get("1.0","end-1c")); t.close()
            self.current_file=t.name; self._update_title()
        self._do_save(self.current_file)
        self._log(f"\n{'─'*52}\n▶  {os.path.basename(self.current_file)}\n{'─'*52}\n", self.BLUE)
        cmd = [sys.executable, (sys.executable if getattr(sys,"frozen",False) else os.path.abspath(__file__)), self.current_file]
        if getattr(sys,"frozen",False): cmd = [sys.executable, self.current_file]
        kw = {}
        if platform.system()=="Windows": kw["creationflags"]=0x08000000
        try:
            self.proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True, bufsize=1, **kw)
            self.run_btn.config(state="disabled")
            self.stop_btn.config(state="normal")
            self.sl.config(text="▶ Running", fg=self.GREEN)
            threading.Thread(target=self._read_output, daemon=True).start()
        except Exception as ex: self._log(f"Launch failed: {ex}\n", self.RED)

    def _read_output(self):
        try:
            for line in self.proc.stdout: self.root.after(0, self._log, line)
        except: pass
        finally: self.root.after(0, self._run_done)

    def _run_done(self):
        code = self.proc.returncode if self.proc else 0
        col  = self.GREEN if code==0 else self.RED
        self._log(f"{'─'*52}\n■  Finished  (exit {code})\n{'─'*52}\n", col)
        self.run_btn.config(state="normal")
        self.stop_btn.config(state="disabled")
        self.sl.config(text="Ready", fg=self.DIM2)

    def stop_script(self, e=None):
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()
            self._log("\n■  Stopped.\n", self.RED)
            self.run_btn.config(state="normal")
            self.stop_btn.config(state="disabled")
            self.sl.config(text="Stopped", fg=self.RED)

    # ─────────────────────────────────────────────────────────────────────
    # CONSOLE
    # ─────────────────────────────────────────────────────────────────────
    def _log(self, text, color="#86efac"):
        self.console.config(state="normal")
        tag = f"c{color.replace('#','')}"
        self.console.tag_config(tag, foreground=color)
        self.console.insert("end", text, tag)
        self.console.see("end")
        self.console.config(state="disabled")

    def _clear_console(self):
        self.console.config(state="normal")
        self.console.delete("1.0","end")
        self.console.config(state="disabled")

    def _copy_console(self):
        text = self.console.get("1.0","end")
        self.root.clipboard_clear(); self.root.clipboard_append(text)

    # ─────────────────────────────────────────────────────────────────────
    # CLOSE
    # ─────────────────────────────────────────────────────────────────────
    def _on_close(self):
        if self.modified and not messagebox.askyesno("Quit","Unsaved changes — quit anyway?"): return
        if self.proc and self.proc.poll() is None: self.proc.terminate()
        self.root.destroy()


# ═════════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ═════════════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    if len(sys.argv) > 1 and os.path.isfile(sys.argv[1]):
        engine = QukEnginePro(sys.argv[1])
        engine.run()
    else:
        QukStudio()
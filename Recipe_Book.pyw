#!/usr/bin/env python3
"""
Recipe collector.

Open the recipe window (the normal way to use it):
    python recipe_collector.py

Or use the command line:
    python recipe_collector.py add <url>
    python recipe_collector.py list
    python recipe_collector.py remove <id or name>
    python recipe_collector.py tag <id or name> <protein|dish_type|cuisine> <value>
    python recipe_collector.py retag      Re-apply the tag rules to every saved recipe
    python recipe_collector.py build      Download any missing thumbnails, rebuild index.html

Setup (once):
    pip install requests beautifulsoup4 pillow

Files in this folder:
    recipe_collector.py   this script
    recipes_phone.html    the phone page template (edit this to change the phone design)
    recipes.json          your collection (back this up)
    index.html            generated page to upload to GitHub Pages
    images/               small recipe photos made by this script (upload these too)
    sw.js, manifest.webmanifest, icon-*.png
                          generated; they let the phone use the page offline
                          and add it to the home screen (upload these too)
"""

import hashlib
import html
import json
from io import BytesIO
import queue
import re
import sys
import threading
import uuid
import webbrowser
from datetime import date
from pathlib import Path
from urllib.parse import urlparse

import requests
from bs4 import BeautifulSoup

try:
    from PIL import Image, ImageDraw, ImageOps
except ImportError:  # recipes still work, but no thumbnails are made
    Image = None

try:
    import tkinter as tk
    from tkinter import messagebox, simpledialog, ttk
except ImportError:  # the window won't open, but the command line still works
    tk = None

BASE = Path(__file__).resolve().parent
DATA_FILE = BASE / "recipes.json"
TEMPLATE_FILE = BASE / "recipes_phone.html"
PAGE_FILE = BASE / "index.html"
THUMB_DIR = BASE / "images"
SW_FILE = BASE / "sw.js"
MANIFEST_FILE = BASE / "manifest.webmanifest"
ICON_SIZES = (192, 512)

THUMB_WIDTH = 480      # pixels; plenty for a phone card, about 20-40 KB each
THUMB_QUALITY = 72

NUTRITION_LABELS = {
    "calories": "Calories",
    "fatContent": "Fat",
    "saturatedFatContent": "Saturated fat",
    "cholesterolContent": "Cholesterol",
    "sodiumContent": "Sodium",
    "carbohydrateContent": "Carbs",
    "fiberContent": "Fiber",
    "sugarContent": "Sugar",
    "proteinContent": "Protein",
}

TAG_FIELDS = ("protein", "dish_type", "cuisine")

# ---------- tag rules ----------
# Protein is a keyword guess from the name and ingredients.
# Eggs are checked separately, only when no meat or tofu is found.
PROTEIN_WORDS = {
    "Chicken": ["chicken"],
    "Turkey": ["turkey"],
    "Beef": ["beef", "steak", "brisket"],
    "Pork": ["pork", "bacon", "ham", "sausage", "pancetta", "prosciutto"],
    "Lamb": ["lamb"],
    "Fish": ["salmon", "tuna", "cod", "tilapia", "halibut", "trout", "fish", "snapper"],
    "Shellfish": ["shrimp", "prawn", "scallop", "crab", "lobster", "mussel", "clam"],
    "Tofu": ["tofu", "tempeh"],
}

EGG_WORDS = ["egg"]

# Phrases that contain a protein word but aren't the protein itself.
NOT_PROTEIN = re.compile(
    r"\b(chicken|beef|pork|vegetable|turkey|fish|shrimp)\s+(broth|stock|bouillon)\b"
    r"|\bfish sauce\b|\begg noodles?\b",
    re.IGNORECASE,
)

# Each rule maps a label to the words that trigger it. The first match wins,
# so put specific words (Latin American) before general ones (American).
CUISINE_RULES = [
    ("Italian", ["italian", "italy", "sicilian", "tuscan"]),
    ("French", ["french", "france", "parisian", "provencal", "provençal"]),
    ("Spanish", ["spanish", "spain", "tapas", "catalan"]),
    ("Greek", ["greek", "greece"]),
    ("Mediterranean", ["mediterranean"]),
    ("British", ["british", "english", "scottish", "scotland", "welsh", "wales",
                 "england", "uk", "britain", "cornish"]),
    ("Irish", ["irish", "ireland"]),
    ("German", ["german", "germany", "bavarian"]),
    ("Eastern European", ["eastern european", "polish", "russian", "hungarian",
                          "ukrainian", "czech"]),
    ("Mexican", ["mexican", "mexico"]),
    ("Caribbean", ["caribbean", "jamaican", "cuban", "puerto rican", "haitian", "trinidad"]),
    ("Latin American", ["latin american", "latin", "south american", "peruvian",
                        "brazilian", "argentinian", "argentine", "colombian", "chilean"]),
    ("Chinese", ["chinese", "cantonese", "szechuan", "sichuan", "hunan", "dim sum", "hong kong"]),
    ("Japanese", ["japanese", "japan"]),
    ("Korean", ["korean", "korea"]),
    ("Thai", ["thai", "thailand"]),
    ("Vietnamese", ["vietnamese", "vietnam"]),
    ("Indian", ["indian", "india", "punjabi", "bengali", "gujarati", "tamil", "keralan"]),
    ("Middle Eastern", ["middle eastern", "lebanese", "persian", "iranian", "turkish",
                        "israeli", "syrian", "egyptian", "levantine"]),
    ("African", ["african", "ethiopian", "moroccan", "nigerian", "kenyan",
                 "south african", "west african"]),
    ("Asian", ["asian", "southeast asian", "pan-asian", "filipino", "indonesian",
               "malaysian", "singaporean"]),
    ("American", ["american", "southern", "cajun", "creole", "bbq", "barbecue",
                  "barbeque", "tex-mex", "tex mex", "soul food", "hawaiian", "new england"]),
]

DISH_RULES = [
    ("Breakfast", ["breakfast", "brunch", "pancake", "waffle", "oatmeal", "granola"]),
    ("Dessert", ["dessert", "desserts", "sweets", "cake", "cookie", "cookies", "pastry",
                 "candy", "frosting", "icing", "ice cream", "brownie", "pudding",
                 "cheesecake", "fudge", "tart"]),
    ("Drink", ["drink", "drinks", "beverage", "cocktail", "smoothie", "juice", "lemonade", "shake"]),
    ("Bread", ["bread", "rolls", "biscuits", "scones", "flatbread", "focaccia", "cornbread"]),
    ("Sauce", ["sauce", "sauces", "dressing", "condiment", "gravy", "marinade", "salsa",
               "pesto", "vinaigrette", "glaze"]),
    ("Soup", ["soup", "soups", "chowder", "bisque", "broth"]),
    ("Salad", ["salad", "salads", "slaw"]),
    ("Appetizer", ["appetizer", "appetizers", "appetiser", "starter", "starters", "dip", "dips",
                   "hors d'oeuvre", "canape", "finger food", "bruschetta", "tapas"]),
    ("Snack", ["snack", "snacks"]),
    ("Side", ["side", "sides", "side dish", "side dishes"]),
    ("Entree", ["main course", "main dish", "main", "mains", "entree", "entrée", "entrees",
                "dinner", "lunch", "supper"]),
]


# ---------- keyword cleanup ----------
# Many sites stuff their keywords with internal junk ("contentId: ...",
# "sponsored: false", "TOTALTIME: 00:40:00"). Keep plain keywords and the few
# labelled ones that describe the food.

KEEP_LABELS = ("occasion", "category", "cuisine", "diet")


def clean_keywords(keywords):
    kept, seen = [], set()
    for k in keywords or []:
        k = (k or "").strip()
        if not k or len(k) > 120:
            continue
        label = k.split(":", 1)[0].strip().lower() if ":" in k else ""
        if label and label not in KEEP_LABELS:
            continue
        if k.lower() not in seen:
            seen.add(k.lower())
            kept.append(k)
    return kept


# ---------- tag helpers ----------

def has_word(text, words):
    pattern = r"\b(" + "|".join(re.escape(w) for w in words) + r")(s|es)?\b"
    return re.search(pattern, text, re.IGNORECASE) is not None


def classify(rules, texts, default):
    """Check each text in order against the rules and return the first label that matches."""
    for text in texts:
        lower = (text or "").lower()
        for label, words in rules:
            if has_word(lower, words):
                return label
    return default


def detect_proteins(name, ingredients):
    text = NOT_PROTEIN.sub(" ", " ".join([name] + ingredients))
    found = [label for label, words in PROTEIN_WORDS.items() if has_word(text, words)]
    if found:
        return found
    if has_word(text, EGG_WORDS):
        return ["Other"]
    return ["Vegan"]


def tidy_label(text):
    """Makes 'main course' and 'Main Course' the same filter option."""
    first = text.split(",")[0]
    return " ".join(w.capitalize() for w in first.split())


# ---------- parsing helpers ----------

def clean(text):
    """Strip HTML tags, decode entities, collapse whitespace."""
    text = re.sub(r"<[^>]+>", " ", str(text))
    return re.sub(r"\s+", " ", html.unescape(text)).strip()


def as_list(value):
    if value is None:
        return []
    return value if isinstance(value, list) else [value]


def text_of(value):
    if isinstance(value, dict):
        value = value.get("name") or value.get("@value") or ""
    return clean(value) if value else ""


def iso_minutes(value):
    """Convert an ISO 8601 duration like 'PT1H30M' into minutes."""
    match = re.fullmatch(r"P(?:(\d+)D)?T?(?:(\d+)H)?(?:(\d+)M)?", str(value or "").strip().upper())
    if not match:
        return None
    days, hours, mins = (int(g) if g else 0 for g in match.groups())
    return days * 1440 + hours * 60 + mins or None


def flatten_steps(instructions):
    steps = []
    for item in as_list(instructions):
        if isinstance(item, str):
            steps.append(clean(item))
        elif isinstance(item, dict):
            if "itemListElement" in item:  # HowToSection groups steps under a heading
                steps.extend(flatten_steps(item["itemListElement"]))
            else:
                steps.append(text_of(item.get("text") or item.get("name")))
    return [s for s in steps if s]


def first_image(value):
    for item in as_list(value):
        url = item if isinstance(item, str) else (item or {}).get("url")
        if url:
            return url
    return ""


# ---------- fetching ----------

def find_recipe_node(data):
    """Recipe data can be nested in lists or an @graph, so search for it."""
    if isinstance(data, list):
        for item in data:
            found = find_recipe_node(item)
            if found:
                return found
    elif isinstance(data, dict):
        if "@graph" in data:
            return find_recipe_node(data["@graph"])
        types = data.get("@type", [])
        if isinstance(types, str):
            types = [types]
        if "Recipe" in types:
            return data
    return None


def fetch_recipe(url):
    headers = {"User-Agent": "Mozilla/5.0 (personal recipe collector)"}
    response = requests.get(url, headers=headers, timeout=20)
    response.raise_for_status()
    soup = BeautifulSoup(response.text, "html.parser")
    for tag in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(tag.get_text() or "")
        except json.JSONDecodeError:
            continue
        node = find_recipe_node(data)
        if node:
            return node
    raise ValueError("no recipe data found on that page")


def build_record(url, node):
    name = text_of(node.get("name")) or "Untitled recipe"
    ingredients = [c for c in (clean(i) for i in as_list(node.get("recipeIngredient"))) if c]
    steps = flatten_steps(node.get("recipeInstructions"))

    prep = iso_minutes(node.get("prepTime"))
    cook = iso_minutes(node.get("cookTime"))
    total = iso_minutes(node.get("totalTime")) or ((prep or 0) + (cook or 0)) or None

    yields = [clean(y) for y in as_list(node.get("recipeYield")) if clean(y)]
    # Prefer the entry with words in it ("4 servings") over a bare number ("4")
    yield_text = next((y for y in yields if re.search(r"[a-z]", y, re.I)), yields[0] if yields else "")

    kws = node.get("keywords") or []
    if isinstance(kws, str):
        kws = kws.split(",")
    keywords = clean_keywords(clean(k) for k in kws if clean(k))

    agg = node.get("aggregateRating") or {}
    try:
        rating = round(float(agg.get("ratingValue")), 1)
    except (TypeError, ValueError, AttributeError):
        rating = None

    nut = node.get("nutrition") or {}
    nutrition = [[label, clean(nut[key])] for key, label in NUTRITION_LABELS.items() if nut.get(key)]

    cuisine_raw = " ".join(text_of(c) for c in as_list(node.get("recipeCuisine")))
    dish_raw = " ".join(text_of(c) for c in as_list(node.get("recipeCategory")))

    return {
        "id": uuid.uuid4().hex[:8],
        "name": name,
        "url": url,
        "source": urlparse(url).netloc.removeprefix("www."),
        "image": first_image(node.get("image")),
        "description": text_of(node.get("description")),
        "dish_type": classify(DISH_RULES, [dish_raw, name], "Other"),
        "cuisine": classify(CUISINE_RULES, [cuisine_raw, *keywords, name], "Other"),
        "protein": detect_proteins(name, ingredients),
        "manual": [],  # tags you set by hand; these survive re-adds and retag
        "prep_min": prep,
        "cook_min": cook,
        "total_min": total,
        "yield": yield_text,
        "rating": rating,
        "keywords": keywords,
        "nutrition": nutrition,
        "ingredients": ingredients,
        "steps": steps,
        "added": date.today().isoformat(),
    }


# ---------- storage ----------

def load():
    if DATA_FILE.exists():
        return json.loads(DATA_FILE.read_text(encoding="utf-8"))
    return []


def save(records):
    DATA_FILE.write_text(json.dumps(records, indent=2, ensure_ascii=False), encoding="utf-8")


def upsert(records, new):
    for i, old in enumerate(records):
        if old["url"] == new["url"]:
            # Keep the old ID and date, plus any tags set by hand.
            new["id"], new["added"] = old["id"], old["added"]
            manual = old.get("manual", [])
            for field in manual:
                new[field] = old.get(field, new[field])
            new["manual"] = manual
            records[i] = new
            return "updated"
    records.append(new)
    return "added"


def find_recipe(records, key):
    key = key.lower()
    matches = [r for r in records if r["id"] == key] or [r for r in records if key in r["name"].lower()]
    if len(matches) != 1:
        raise ValueError(f"'{key}' matched {len(matches)} recipes. Use the ID from 'list' instead.")
    return matches[0]


def set_tag(recipe, field, value):
    if field not in TAG_FIELDS:
        raise ValueError("Field must be protein, dish_type, or cuisine.")
    if field == "protein":
        values = [v.strip() for v in value.split(",") if v.strip()]
        recipe["protein"] = [v.title() for v in values] or ["Vegan"]
    else:
        rules = CUISINE_RULES if field == "cuisine" else DISH_RULES
        recipe[field] = classify(rules, [value], "") or tidy_label(value) or "Other"
    recipe.setdefault("manual", [])
    if field not in recipe["manual"]:
        recipe["manual"].append(field)


def retag_all(records):
    """Re-apply the tag rules to every recipe. Tags set by hand are left alone."""
    for r in records:
        r["keywords"] = clean_keywords(r.get("keywords", []))
        manual = r.get("manual", [])
        if "protein" not in manual:
            r["protein"] = detect_proteins(r["name"], r.get("ingredients", []))
        if "dish_type" not in manual:
            r["dish_type"] = classify(DISH_RULES, [r.get("dish_type", ""), r["name"]], "Other")
        if "cuisine" not in manual:
            r["cuisine"] = classify(CUISINE_RULES,
                                    [r.get("cuisine", ""), *r.get("keywords", []), r["name"]], "Other")
    return len(records)


# ---------- thumbnails ----------

def thumb_name(record):
    return f"images/{record['id']}.jpg"


def fetch_thumb(record):
    """Download the recipe photo and save a small JPEG. Returns True on success."""
    url = record.get("image") or ""
    if not url:
        return False
    if url.startswith("//"):
        url = "https:" + url
    headers = {"User-Agent": "Mozilla/5.0 (personal recipe collector)"}
    response = requests.get(url, headers=headers, timeout=20)
    response.raise_for_status()
    img = ImageOps.exif_transpose(Image.open(BytesIO(response.content))).convert("RGB")
    if img.width > THUMB_WIDTH:
        height = round(img.height * THUMB_WIDTH / img.width)
        img = img.resize((THUMB_WIDTH, height), Image.LANCZOS)
    THUMB_DIR.mkdir(exist_ok=True)
    img.save(BASE / thumb_name(record), "JPEG", quality=THUMB_QUALITY,
             optimize=True, progressive=True)
    return True


def ensure_thumbs(records, log=print):
    """Make a thumbnail for every recipe that lacks one. Returns how many were made.

    The caller should save(records) afterwards so each recipe remembers its thumb."""
    if Image is None:
        log("Pillow isn't installed, so no thumbnails were made (pip install pillow).")
        return 0
    made = 0
    for r in records:
        path = BASE / thumb_name(r)
        if not path.exists():
            try:
                if not fetch_thumb(r):
                    continue
                made += 1
            except Exception as err:
                log(f"No thumbnail for {r['name']}: {err}")
                continue
        r["thumb"] = thumb_name(r)
    if made:
        log(f"Saved {made} thumbnail(s).")
    return made


def remove_thumb(record):
    try:
        (BASE / thumb_name(record)).unlink()
    except OSError:
        pass


def add_recipe(url):
    """Fetch, save, and rebuild the page. Returns (result, record). Raises on failure."""
    if not url.startswith(("http://", "https://")):
        url = "https://" + url
    record = build_record(url, fetch_recipe(url))
    records = load()
    result = upsert(records, record)
    ensure_thumbs(records)
    save(records)
    build_page(records)
    return result, record


# ---------- phone page ----------

def make_icons():
    """Draw a simple plate icon for the home screen, unless you've supplied your own."""
    if Image is None:
        return
    for size in ICON_SIZES:
        path = BASE / f"icon-{size}.png"
        if path.exists():
            continue
        img = Image.new("RGB", (size, size), "#0f6e56")
        draw = ImageDraw.Draw(img)
        c, r = size / 2, size * 0.30
        draw.ellipse([c - r, c - r, c + r, c + r], fill="#ffffff")
        r2 = size * 0.20
        draw.ellipse([c - r2, c - r2, c + r2, c + r2], fill="#0f6e56")
        r3 = size * 0.17
        draw.ellipse([c - r3, c - r3, c + r3, c + r3], fill="#e4f2ec")
        img.save(path, "PNG")


SW_TEMPLATE = """// Generated by the recipe script. Do not edit.
const CACHE = "recipes-__VERSION__";
const FILES = __FILES__;

self.addEventListener("install", e => {
  e.waitUntil(
    caches.open(CACHE)
      .then(c => Promise.all(FILES.map(f =>
        c.add(new Request(f, { cache: "reload" })).catch(() => {}))))
      .then(() => self.skipWaiting())
  );
});

self.addEventListener("activate", e => {
  e.waitUntil(
    caches.keys()
      .then(keys => Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

self.addEventListener("fetch", e => {
  const req = e.request;
  if (req.method !== "GET" || new URL(req.url).origin !== location.origin) return;

  if (req.mode === "navigate") {
    // Newest page if the network answers quickly, otherwise the saved copy.
    const network = fetch(req).then(res => {
      const copy = res.clone();
      caches.open(CACHE).then(c => c.put("index.html", copy));
      return res;
    });
    const timeout = new Promise((_, reject) => setTimeout(reject, 3000));
    e.respondWith(
      Promise.race([network, timeout]).catch(() =>
        caches.match("index.html").then(hit => hit || network))
    );
    return;
  }

  // Photos, icons, manifest: saved copy first.
  e.respondWith(caches.match(req).then(hit => hit || fetch(req)));
});
"""


def write_offline_files(records, page_text):
    make_icons()
    icons = [f"icon-{n}.png" for n in ICON_SIZES if (BASE / f"icon-{n}.png").exists()]
    thumbs = sorted(r["thumb"] for r in records if r.get("thumb") and (BASE / r["thumb"]).exists())
    files = ["./", "index.html", "manifest.webmanifest", *icons, *thumbs]

    # The version changes whenever the page or its photos change, which is what
    # makes the phone download the update.
    stamp = hashlib.sha1(page_text.encode("utf-8"))
    for t in thumbs:
        stamp.update(t.encode() + str((BASE / t).stat().st_size).encode())
    sw = SW_TEMPLATE.replace("__VERSION__", stamp.hexdigest()[:10]) \
                    .replace("__FILES__", json.dumps(files, indent=2))
    SW_FILE.write_text(sw, encoding="utf-8")

    manifest = {
        "name": "Recipes",
        "short_name": "Recipes",
        "start_url": "./",
        "scope": "./",
        "display": "standalone",
        "background_color": "#f6f6f3",
        "theme_color": "#0f6e56",
        "icons": [{"src": i, "sizes": i.split("-")[1].split(".")[0] + "x" + i.split("-")[1].split(".")[0],
                   "type": "image/png", "purpose": "any maskable"} for i in icons],
    }
    MANIFEST_FILE.write_text(json.dumps(manifest, indent=2), encoding="utf-8")


def slim(record):
    """The copy of a recipe that goes into the phone page: only what the page uses."""
    r = {k: v for k, v in record.items() if k not in ("manual", "added")}
    r["keywords"] = clean_keywords(r.get("keywords", []))
    thumb = r.get("thumb")
    if thumb and (BASE / thumb).exists():
        r.pop("image", None)   # no need to carry the web address as well
    else:
        r.pop("thumb", None)
    return r


def build_page(records):
    if not TEMPLATE_FILE.exists():
        raise FileNotFoundError(f"{TEMPLATE_FILE.name} is missing. It must be in the same folder as this script.")
    ordered = sorted((slim(r) for r in records), key=lambda r: r["name"].lower())
    # Escaping "</" keeps recipe text from closing the script tag early.
    data = json.dumps(ordered, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    template = TEMPLATE_FILE.read_text(encoding="utf-8")
    page = template.replace("__RECIPE_DATA__", data)
    PAGE_FILE.write_text(page, encoding="utf-8")
    write_offline_files(ordered, page)


# ---------- command line ----------

def run_cli(args):
    cmd, rest = args[0], args[1:]
    try:
        if cmd == "add" and len(rest) == 1:
            result, record = add_recipe(rest[0])
            print(f"{result.capitalize()}: {record['name']} (id {record['id']})")
            print(f"  protein: {', '.join(record['protein'])}")
            print(f"  dish type: {record['dish_type']}   cuisine: {record['cuisine']}")

        elif cmd == "list":
            for r in sorted(load(), key=lambda r: r["name"].lower()):
                tags = f"{', '.join(r['protein'])} | {r['dish_type']} | {r['cuisine']}"
                print(f"{r['id']}  {r['name']}  [{tags}]")

        elif cmd == "remove" and len(rest) == 1:
            records = load()
            recipe = find_recipe(records, rest[0])
            records.remove(recipe)
            remove_thumb(recipe)
            save(records)
            build_page(records)
            print(f"Removed {recipe['name']}")

        elif cmd == "tag" and len(rest) == 3:
            records = load()
            recipe = find_recipe(records, rest[0])
            set_tag(recipe, rest[1], rest[2])
            save(records)
            build_page(records)
            print(f"Updated {recipe['name']}")

        elif cmd == "retag":
            records = load()
            count = retag_all(records)
            save(records)
            build_page(records)
            print(f"Re-applied tag rules to {count} recipes.")

        elif cmd == "build":
            records = load()
            ensure_thumbs(records)
            save(records)
            build_page(records)
            print(f"Rebuilt {PAGE_FILE.name} with {len(records)} recipes.")

        else:
            print(__doc__)
    except Exception as err:
        sys.exit(f"Error: {err}")


# ---------- window ----------

class RecipeApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Recipe Collector")
        self.root.geometry("680x600")
        self.root.minsize(520, 460)

        self.events = queue.Queue()   # messages from background work
        self.busy = False
        self.shown = []               # recipes in the same order as the list box

        self.build_ui()
        self.refresh_list()
        self.root.after(100, self.poll_events)

    # ---------- layout ----------

    def build_ui(self):
        top = ttk.LabelFrame(self.root, text="Add a recipe")
        top.pack(fill="x", padx=10, pady=(10, 4))

        self.url_var = tk.StringVar()
        self.url_entry = ttk.Entry(top, textvariable=self.url_var)
        self.url_entry.pack(side="left", fill="x", expand=True, padx=(8, 4), pady=8)
        self.url_entry.bind("<Return>", lambda e: self.add_clicked())
        self.url_entry.focus_set()

        ttk.Button(top, text="Paste", command=self.paste_clicked).pack(side="left", padx=2, pady=8)
        self.add_button = ttk.Button(top, text="Add recipe", command=self.add_clicked)
        self.add_button.pack(side="left", padx=(2, 8), pady=8)

        self.status = ttk.Label(self.root, text="Paste a recipe URL and press Add.")
        self.status.pack(fill="x", padx=12, pady=(2, 6))

        middle = ttk.LabelFrame(self.root, text="Your recipes")
        middle.pack(fill="both", expand=True, padx=10, pady=4)

        list_frame = ttk.Frame(middle)
        list_frame.pack(fill="both", expand=True, padx=8, pady=8)
        scroll = ttk.Scrollbar(list_frame, orient="vertical")
        self.listbox = tk.Listbox(list_frame, activestyle="none", font=("Segoe UI", 10),
                                  yscrollcommand=scroll.set, selectmode="extended")
        scroll.config(command=self.listbox.yview)
        self.listbox.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

        buttons = ttk.Frame(middle)
        buttons.pack(fill="x", padx=8, pady=(0, 8))
        ttk.Button(buttons, text="Edit tags", command=self.edit_tags_clicked).pack(side="left")
        ttk.Button(buttons, text="Re-apply tags", command=self.retag_clicked).pack(side="left", padx=6)
        ttk.Button(buttons, text="Remove selected", command=self.remove_clicked).pack(side="left")
        ttk.Button(buttons, text="Open page in browser", command=self.open_page_clicked).pack(side="right")
        ttk.Button(buttons, text="Rebuild page", command=self.rebuild_clicked).pack(side="right", padx=6)

        log_frame = ttk.LabelFrame(self.root, text="Log")
        log_frame.pack(fill="x", padx=10, pady=(4, 10))
        self.log_box = tk.Text(log_frame, height=6, state="disabled", wrap="word")
        self.log_box.pack(fill="x", padx=8, pady=8)

    # ---------- helpers ----------

    def log(self, message):
        self.log_box.config(state="normal")
        self.log_box.insert("end", message + "\n")
        self.log_box.see("end")
        self.log_box.config(state="disabled")

    def set_busy(self, busy):
        self.busy = busy
        self.add_button.config(state="disabled" if busy else "normal")
        self.status.config(text="Working..." if busy else "Ready.")

    def refresh_list(self):
        self.shown = sorted(load(), key=lambda r: r["name"].lower())
        self.listbox.delete(0, "end")
        for r in self.shown:
            tags = f"{', '.join(r['protein'])} · {r['dish_type']} · {r['cuisine']}"
            self.listbox.insert("end", f"{r['name']}   [{tags}]")

    def selected_records(self):
        return [self.shown[i] for i in self.listbox.curselection()]

    def check_not_busy(self):
        if self.busy:
            messagebox.showinfo("Please wait", "A recipe is still being saved. Try again in a moment.")
            return False
        return True

    # ---------- actions ----------

    def paste_clicked(self):
        try:
            text = self.root.clipboard_get()
        except tk.TclError:
            self.log("Nothing on the clipboard to paste.")
            return
        self.url_var.set(text.strip())
        self.url_entry.icursor("end")

    def add_clicked(self):
        if not self.check_not_busy():
            return
        url = self.url_var.get().strip()
        if not url:
            self.log("Paste a recipe URL first.")
            return

        self.set_busy(True)
        self.log(f"Fetching {url}")

        def work():
            try:
                result, record = add_recipe(url)
                self.events.put(("ok", f"{result.capitalize()}: {record['name']} "
                                       f"(protein: {', '.join(record['protein'])}, "
                                       f"dish: {record['dish_type']}, cuisine: {record['cuisine']})"))
            except Exception as err:  # keep the window open whatever goes wrong
                self.events.put(("error", f"Couldn't save that recipe: {err}"))

        threading.Thread(target=work, daemon=True).start()

    def remove_clicked(self):
        if not self.check_not_busy():
            return
        picked = self.selected_records()
        if not picked:
            self.log("Select one or more recipes to remove first.")
            return
        names = "\n".join(r["name"] for r in picked)
        if not messagebox.askyesno("Remove recipes", f"Remove these recipes?\n\n{names}"):
            return
        try:
            ids = {r["id"] for r in picked}
            records = [r for r in load() if r["id"] not in ids]
            for r in picked:
                remove_thumb(r)
            save(records)
            build_page(records)
            self.refresh_list()
            self.log(f"Removed {len(picked)} recipe(s).")
        except Exception as err:
            self.log(f"Error: {err}")

    def edit_tags_clicked(self):
        if not self.check_not_busy():
            return
        picked = self.selected_records()
        if len(picked) != 1:
            self.log("Select exactly one recipe to edit its tags.")
            return
        target = picked[0]
        protein = simpledialog.askstring(
            "Protein", "Protein (e.g. Chicken, or Tofu. Separate several with commas. Leave blank for Vegan):",
            initialvalue=", ".join(target["protein"]), parent=self.root)
        if protein is None:
            return
        dish = simpledialog.askstring("Dish type", "Dish type (e.g. Entree, Soup, Dessert):",
                                      initialvalue=target["dish_type"], parent=self.root)
        if dish is None:
            return
        cuisine = simpledialog.askstring("Cuisine", "Cuisine (e.g. Italian, Asian, American):",
                                         initialvalue=target["cuisine"], parent=self.root)
        if cuisine is None:
            return
        try:
            records = load()
            recipe = next(r for r in records if r["id"] == target["id"])
            set_tag(recipe, "protein", protein)
            set_tag(recipe, "dish_type", dish)
            set_tag(recipe, "cuisine", cuisine)
            save(records)
            build_page(records)
            self.refresh_list()
            self.log(f"Updated tags for {target['name']}.")
        except Exception as err:
            self.log(f"Error: {err}")

    def retag_clicked(self):
        if not self.check_not_busy():
            return
        if not messagebox.askyesno(
                "Re-apply tags",
                "Recalculate protein, dish type, and cuisine for every recipe?\n\n"
                "Tags you set with Edit tags are kept."):
            return
        try:
            records = load()
            count = retag_all(records)
            save(records)
            build_page(records)
            self.refresh_list()
            self.log(f"Re-applied tag rules to {count} recipe(s).")
        except Exception as err:
            self.log(f"Error: {err}")

    def rebuild_clicked(self):
        try:
            records = load()
            self.log("Checking thumbnails...")
            self.root.update_idletasks()
            ensure_thumbs(records, log=self.log)
            save(records)
            build_page(records)
            self.log(f"Rebuilt {PAGE_FILE.name}.")
        except Exception as err:
            self.log(f"Error: {err}")

    def open_page_clicked(self):
        try:
            if not PAGE_FILE.exists():
                build_page(load())
            webbrowser.open(PAGE_FILE.as_uri())
        except Exception as err:
            self.log(f"Error: {err}")

    # ---------- background results ----------

    def poll_events(self):
        try:
            while True:
                kind, message = self.events.get_nowait()
                self.log(message)
                self.set_busy(False)
                if kind == "ok":
                    self.url_var.set("")
                    self.refresh_list()
        except queue.Empty:
            pass
        self.root.after(100, self.poll_events)


# ---------- entry point ----------

def main():
    args = sys.argv[1:]
    if not args:
        if tk is None:
            sys.exit("The window needs tkinter. Use the command line instead (see the help text).")
        root = tk.Tk()
        RecipeApp(root)
        root.mainloop()
    elif args[0] in ("-h", "--help", "help"):
        print(__doc__)
    else:
        run_cli(args)


if __name__ == "__main__":
    main()
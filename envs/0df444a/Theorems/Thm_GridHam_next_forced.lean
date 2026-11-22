-- Prove2me | Theorems.Thm_GridHam_next_forced
-- name    : GridHam.next_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:07:04.177055+00:00
-- url     : https://prove2.me/theorems/caf68230-0a4e-4ef2-bb15-5fa8fefbfd1b
-- title:
--   Grid Ham: next forced
-- statement:
--   **Forced successor.** A middle cell whose predecessor is `a` and whose
--   only possible path neighbours are `a` and `b` is followed by `b`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L234-L243
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L234-L243

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.next_forced {p : List Coord} {a x b : Coord} (hnd : p.Nodup)
    (hch : chainAdjacent p = true) (hx : x ∈ p) (hxh : p.head? ≠ some x)
    (hxl : p.getLast? ≠ some x) (hprev : PNext p a x)
    (hnb : ∀ y ∈ p, Adjacent x y → y = a ∨ y = b) : PNext p x b := by sorry

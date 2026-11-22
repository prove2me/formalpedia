-- Prove2me | Theorems.Thm_GridHam_forced_after_head
-- name    : GridHam.forced_after_head
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:46:13.680176+00:00
-- url     : https://prove2.me/theorems/4cb10ae7-a5a2-4adf-ba92-052784709d87
-- title:
--   Grid Ham: forced after head
-- statement:
--   **Forced move.** If a middle cell `x` can only be path-adjacent to the
--   first cell `u` or to one other cell `z`, then `x` comes right after `u`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L165-L178
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L165-L178

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.forced_after_head {p : List Coord} {u x z : Coord} (hnd : p.Nodup)
    (hch : chainAdjacent p = true) (hh : p.head? = some u) (hx : x ∈ p)
    (hxh : p.head? ≠ some x) (hxl : p.getLast? ≠ some x)
    (hnb : ∀ y ∈ p, Adjacent y x → y = u ∨ y = z) : PNext p u x := by sorry

-- Prove2me | Theorems.Thm_GridHam_splitVertically_preserves_startRight
-- name    : GridHam.splitVertically_preserves_startRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:24:37.401931+00:00
-- url     : https://prove2.me/theorems/c37a63da-10b2-4b0b-abe7-837f3dc4ec55
-- title:
--   Grid Ham: split Vertically preserves start Right
-- statement:
--   Symmetric to `splitVertically_preserves_startLeft` when `t` is the left
--   endpoint instead (`t.1 < s.1`).
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L413-L423
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L413-L423

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.splitVertically_preserves_startRight
    (width height cut cutRow : ℕ) (s t : Coord)
    (hstartRight : t.1 < s.1)
    (hcutRange : t.1 ≤ cut) (hcutRange' : cut < s.1)
    (hcutRow : cutRow < height)
    (hleft : HasHamPath (cut + 1) height (cut, cutRow) t)
    (hright : HasHamPath (width - (cut + 1)) height (0, cutRow)
      (s.1 - (cut + 1), s.2)) :
    HasHamPath width height s t := by sorry

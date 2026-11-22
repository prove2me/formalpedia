-- Prove2me | Theorems.Thm_GridHam_splitVertically_preserves_startLeft
-- name    : GridHam.splitVertically_preserves_startLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:37:41.742798+00:00
-- url     : https://prove2.me/theorems/69589960-9fe1-44dd-85ca-8d3d3340b4f9
-- title:
--   Grid Ham: split Vertically preserves start Left
-- statement:
--   Splitting vertically at a column edge `(cut, cutRow) – (cut+1, cutRow)`,
--   where `s` is the left endpoint (`s.1 < t.1`) and the cut column is strictly
--   between `s.1` and `t.1`: if the left piece (from `s` to the cut vertex) and
--   the right piece (from the cut's right-neighbor, in coordinates shifted left
--   by `cut+1`, to `t`) are both solvable, so is the whole problem. The path is
--   the left path followed by the right path shifted right by `cut + 1`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L186-L283
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L186-L283

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.splitVertically_preserves_startLeft
    (width height cut cutRow : ℕ) (s t : Coord)
    (_hstartLeft : s.1 < t.1)
    (_hcutRange : s.1 ≤ cut) (hcutRange' : cut < t.1)
    (_hcutRow : cutRow < height)
    (hleft : HasHamPath (cut + 1) height s (cut, cutRow))
    (hright : HasHamPath (width - (cut + 1)) height (0, cutRow)
      (t.1 - (cut + 1), t.2)) :
    HasHamPath width height s t := by sorry

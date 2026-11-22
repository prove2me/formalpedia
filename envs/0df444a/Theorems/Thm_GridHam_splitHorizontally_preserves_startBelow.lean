-- Prove2me | Theorems.Thm_GridHam_splitHorizontally_preserves_startBelow
-- name    : GridHam.splitHorizontally_preserves_startBelow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:54:56.470261+00:00
-- url     : https://prove2.me/theorems/896cc156-ea86-48e3-877c-e9d43166df09
-- title:
--   Grid Ham: split Horizontally preserves start Below
-- statement:
--   Splitting horizontally at a row edge `(cutCol, cut) – (cutCol, cut+1)`,
--   symmetric to `splitVertically_preserves_startLeft` with `s` below `t`
--   (`s.2 < t.2`). `cutCol` is the free parameter here.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L428-L445
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L428-L445

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.splitHorizontally_preserves_startBelow
    (width height cut cutCol : ℕ) (s t : Coord)
    (hstartBelow : s.2 < t.2)
    (hcutRange : s.2 ≤ cut) (hcutRange' : cut < t.2)
    (hcutCol : cutCol < width)
    (hlower : HasHamPath width (cut + 1) s (cutCol, cut))
    (hupper : HasHamPath width (height - (cut + 1)) (cutCol, 0)
      (t.1, t.2 - (cut + 1))) :
    HasHamPath width height s t := by sorry

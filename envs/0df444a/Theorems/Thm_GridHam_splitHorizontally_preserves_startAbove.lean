-- Prove2me | Theorems.Thm_GridHam_splitHorizontally_preserves_startAbove
-- name    : GridHam.splitHorizontally_preserves_startAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:25:40.151726+00:00
-- url     : https://prove2.me/theorems/f0e8c0f9-d7c7-4e9e-849f-f4f378a10eed
-- title:
--   Grid Ham: split Horizontally preserves start Above
-- statement:
--   Symmetric to `splitHorizontally_preserves_startBelow` when `t` is below
--   `s` instead (`t.2 < s.2`).
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L449-L459
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L449-L459

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.splitHorizontally_preserves_startAbove
    (width height cut cutCol : ℕ) (s t : Coord)
    (hstartAbove : t.2 < s.2)
    (hcutRange : t.2 ≤ cut) (hcutRange' : cut < s.2)
    (hcutCol : cutCol < width)
    (hlower : HasHamPath width (cut + 1) t (cutCol, cut))
    (hupper : HasHamPath width (height - (cut + 1)) (cutCol, 0)
      (s.1, s.2 - (cut + 1))) :
    HasHamPath width height s t := by sorry

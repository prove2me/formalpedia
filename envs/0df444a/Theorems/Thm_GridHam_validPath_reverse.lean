-- Prove2me | Theorems.Thm_GridHam_validPath_reverse
-- name    : GridHam.validPath_reverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:43:21.700042+00:00
-- url     : https://prove2.me/theorems/ab488044-2795-4da4-aec4-5159abe144ea
-- title:
--   Grid Ham: valid Path reverse
-- statement:
--   List-level reversal (keeps track of the actual path).
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L753-L767
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L753-L767

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.validPath_reverse {width height : ℕ} {s t : Coord} {p : List Coord}
    (hv : ValidPath width height s t p) : ValidPath width height t s p.reverse := by sorry

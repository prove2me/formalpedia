-- Prove2me | Theorems.Thm_GridHam_hasHamPath_transpose
-- name    : GridHam.hasHamPath_transpose
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:27:38.746309+00:00
-- url     : https://prove2.me/theorems/f4bb0303-2651-4a48-af30-a13df934e88b
-- title:
--   Grid Ham: has Ham Path transpose
-- statement:
--   Transposing a Hamiltonian path on a `width × height` grid gives one on
--   the `height × width` grid.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L371-L409
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L371-L409

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.hasHamPath_transpose {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) :
    HasHamPath height width (swapXY s) (swapXY t) := by sorry

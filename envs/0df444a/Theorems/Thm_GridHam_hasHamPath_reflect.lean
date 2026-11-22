-- Prove2me | Theorems.Thm_GridHam_hasHamPath_reflect
-- name    : GridHam.hasHamPath_reflect
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:43:48.296053+00:00
-- url     : https://prove2.me/theorems/93da1895-2716-4464-b067-76c3ee3b1d64
-- title:
--   Grid Ham: has Ham Path reflect
-- statement:
--   Reflecting a Hamiltonian path left-to-right gives a Hamiltonian path.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L1062-L1116
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L1062-L1116

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.hasHamPath_reflect {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) :
    HasHamPath width height (reflectX width s) (reflectX width t) := by sorry

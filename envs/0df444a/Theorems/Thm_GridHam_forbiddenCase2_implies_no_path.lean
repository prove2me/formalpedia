-- Prove2me | Theorems.Thm_GridHam_forbiddenCase2_implies_no_path
-- name    : GridHam.forbiddenCase2_implies_no_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:13:27.991321+00:00
-- url     : https://prove2.me/theorems/7bfa89fd-298d-43cf-8698-0f7f33be6c64
-- title:
--   Grid Ham: forbidden Case2 implies no path
-- statement:
--   **Forbidden case 2 is really forbidden.**
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L260-L277
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L260-L277

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.forbiddenCase2_implies_no_path (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hf : ForbiddenCase2 width height s t) :
    ¬ HasHamPath width height s t := by sorry

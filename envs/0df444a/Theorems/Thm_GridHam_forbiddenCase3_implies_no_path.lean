-- Prove2me | Theorems.Thm_GridHam_forbiddenCase3_implies_no_path
-- name    : GridHam.forbiddenCase3_implies_no_path
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:13:48.433375+00:00
-- url     : https://prove2.me/theorems/8c6fee94-17cc-4df4-806d-7c9608ee7999
-- title:
--   Grid Ham: forbidden Case3 implies no path
-- statement:
--   **Forbidden case 3 is really forbidden.** Height 3 directly; width 3 by
--   transposing.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L297-L317
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Necessity.lean#L297-L317

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.forbiddenCase3_implies_no_path (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (h3 : width = 3 ∨ height = 3) (hf : ForbiddenCase3 width height s t) :
    ¬ HasHamPath width height s t := by sorry

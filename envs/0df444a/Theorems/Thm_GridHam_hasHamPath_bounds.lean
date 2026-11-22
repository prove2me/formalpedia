-- Prove2me | Theorems.Thm_GridHam_hasHamPath_bounds
-- name    : GridHam.hasHamPath_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:00:31.746261+00:00
-- url     : https://prove2.me/theorems/7c67f1a3-c338-4f32-99f5-b91301961389
-- title:
--   Grid Ham: has Ham Path bounds
-- statement:
--   Both endpoints of a Hamiltonian path are in bounds.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L998-L1007
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L998-L1007

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.hasHamPath_bounds {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) : InBounds width height s ∧ InBounds width height t := by sorry

-- Prove2me | Theorems.Thm_GridHam_forbiddenCase1_h1
-- name    : GridHam.forbiddenCase1_h1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:51:52.121168+00:00
-- url     : https://prove2.me/theorems/af4c98e1-bbd3-4813-aae2-48d63e576414
-- title:
--   Grid Ham: forbidden Case1 h1
-- statement:
--   `ForbiddenCase1` on a height-1 grid whose width is not 1.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L327-L331
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L327-L331

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.forbiddenCase1_h1 (width : ℕ) (s t : Coord) (hw : ¬ width = 1) :
    ForbiddenCase1 width 1 s t ↔
      ¬ ((s = (0, 0) ∧ t = (width - 1, 0)) ∨ (s = (width - 1, 0) ∧ t = (0, 0))) := by sorry

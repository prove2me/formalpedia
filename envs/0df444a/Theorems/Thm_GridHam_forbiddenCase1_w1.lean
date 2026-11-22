-- Prove2me | Theorems.Thm_GridHam_forbiddenCase1_w1
-- name    : GridHam.forbiddenCase1_w1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:51:32.36626+00:00
-- url     : https://prove2.me/theorems/082b70e5-d3a8-442b-b4fe-f3aa42a09ee1
-- title:
--   Grid Ham: forbidden Case1 w1
-- statement:
--   `ForbiddenCase1` on a width-1 grid, with the `let`s and `if`s resolved.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L320-L324
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L320-L324

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.forbiddenCase1_w1 (height : ℕ) (s t : Coord) :
    ForbiddenCase1 1 height s t ↔
      ¬ ((s = (0, 0) ∧ t = (0, height - 1)) ∨ (s = (0, height - 1) ∧ t = (0, 0))) := by sorry

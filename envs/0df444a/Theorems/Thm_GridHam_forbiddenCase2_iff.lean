-- Prove2me | Theorems.Thm_GridHam_forbiddenCase2_iff
-- name    : GridHam.forbiddenCase2_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:41:27.739733+00:00
-- url     : https://prove2.me/theorems/ed195cf7-5c60-4fc4-bf96-53b60299cf5a
-- title:
--   Grid Ham: forbidden Case2 iff
-- statement:
--   The Grid Ham construction uses the forbidden Case2 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L87-L90
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L87-L90

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.forbiddenCase2_iff (w h sx sy tx ty : ℕ) :
    ForbiddenCase2 w h (sx, sy) (tx, ty) ↔ F2A w h sx sy tx ty := by sorry

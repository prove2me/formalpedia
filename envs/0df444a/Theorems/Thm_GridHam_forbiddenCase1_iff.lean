-- Prove2me | Theorems.Thm_GridHam_forbiddenCase1_iff
-- name    : GridHam.forbiddenCase1_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:52:49.915808+00:00
-- url     : https://prove2.me/theorems/a1416a01-2dd8-48c4-a81b-08569e8dabfd
-- title:
--   Grid Ham: forbidden Case1 iff
-- statement:
--   The Grid Ham construction uses the forbidden Case1 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L76-L80
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L76-L80

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.forbiddenCase1_iff (w h sx sy tx ty : ℕ) :
    ForbiddenCase1 w h (sx, sy) (tx, ty) ↔ F1A w h sx sy tx ty := by sorry

-- Prove2me | Theorems.Thm_GridHam_forbiddenCase3_iff
-- name    : GridHam.forbiddenCase3_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:41:28.954584+00:00
-- url     : https://prove2.me/theorems/26e70097-9a8e-4983-b6b4-be85626498f2
-- title:
--   Grid Ham: forbidden Case3 iff
-- statement:
--   The Grid Ham construction uses the forbidden Case3 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L92-L96
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L92-L96

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.forbiddenCase3_iff (w h sx sy tx ty : ℕ) :
    ForbiddenCase3 w h (sx, sy) (tx, ty) ↔ F3A w h sx sy tx ty := by sorry

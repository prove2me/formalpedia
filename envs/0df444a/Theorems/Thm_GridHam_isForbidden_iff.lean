-- Prove2me | Theorems.Thm_GridHam_isForbidden_iff
-- name    : GridHam.isForbidden_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:53:25.727957+00:00
-- url     : https://prove2.me/theorems/474181ce-730f-43ea-b455-cdbf2b4cc41a
-- title:
--   Grid Ham: is Forbidden iff
-- statement:
--   The Grid Ham construction uses the is Forbidden iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L98-L130
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L98-L130

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.isForbidden_iff (w h sx sy tx ty : ℕ) :
    IsForbidden w h (sx, sy) (tx, ty) ↔ ForbA w h sx sy tx ty := by sorry

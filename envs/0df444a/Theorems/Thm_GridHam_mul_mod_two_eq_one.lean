-- Prove2me | Theorems.Thm_GridHam_mul_mod_two_eq_one
-- name    : GridHam.mul_mod_two_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:52:27.449833+00:00
-- url     : https://prove2.me/theorems/190c60f7-67a4-43cd-a565-4732db370d16
-- title:
--   Grid Ham: mul mod two eq one
-- statement:
--   The Grid Ham construction uses the mul mod two eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L26-L30
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean#L26-L30

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.mul_mod_two_eq_one (w h : ℕ) : (w * h) % 2 = 1 ↔ w % 2 = 1 ∧ h % 2 = 1 := by sorry

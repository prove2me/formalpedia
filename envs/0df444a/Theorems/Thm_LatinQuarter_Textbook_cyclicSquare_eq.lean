-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_cyclicSquare_eq
-- name    : LatinQuarter.Textbook.cyclicSquare_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:23:26.07899+00:00
-- url     : https://prove2.me/theorems/9c52d7ec-37ab-4d42-9585-2c90bf0d1e14
-- title:
--   Textbook: cyclic Square eq
-- statement:
--   The Textbook construction uses the cyclic Square eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L88-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L88-L91

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.cyclicSquare_eq (n : ℕ) : cyclicSquare n = cyclic n := by sorry

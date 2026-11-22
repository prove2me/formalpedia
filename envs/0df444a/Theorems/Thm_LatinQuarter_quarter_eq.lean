-- Prove2me | Theorems.Thm_LatinQuarter_quarter_eq
-- name    : LatinQuarter.quarter_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:08.056345+00:00
-- url     : https://prove2.me/theorems/eb0ecad1-c991-4daa-a5aa-24fd14583af4
-- title:
--   Latin Quarter: quarter eq
-- statement:
--   The Latin Quarter construction uses the quarter eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Budget.lean#L20-L27
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Budget.lean#L20-L27

module
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Budget
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators

theorem LatinQuarter.quarter_eq (n : ℕ) : n * n / 4 = (n / 2) * (n - n / 2) := by sorry

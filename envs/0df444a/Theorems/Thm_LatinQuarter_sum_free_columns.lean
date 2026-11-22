-- Prove2me | Theorems.Thm_LatinQuarter_sum_free_columns
-- name    : LatinQuarter.sum_free_columns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:16.697419+00:00
-- url     : https://prove2.me/theorems/5de97d49-31f7-4633-993b-845f14e31c2a
-- title:
--   Latin Quarter: sum free columns
-- statement:
--   The Latin Quarter construction uses the sum free columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Budget.lean#L29-L42
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Budget.lean#L29-L42

module
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Budget
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators

theorem LatinQuarter.sum_free_columns {n : ℕ} (P : Finset (Cell n)) :
    (∑ r, Fintype.card (FreeColumn P r)) + P.card = n * n := by sorry

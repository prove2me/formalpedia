-- Prove2me | Theorems.Thm_LatinQuarter_clue_budget
-- name    : LatinQuarter.clue_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:22.942488+00:00
-- url     : https://prove2.me/theorems/69dfa91c-e82a-45fb-ac6b-e904f2bb5917
-- title:
--   Latin Quarter: clue budget
-- statement:
--   The global clue budget supplies exactly the strict inequality used
--   by the residual-position pigeonhole argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Budget.lean#L46-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Budget.lean#L46-L60

module
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Budget
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators

theorem LatinQuarter.clue_budget {n : ℕ} (P : Finset (Cell n))
    (hP : P.card < n * n / 4) :
    (n - n / 2) * (n - n / 2) <
      ∑ r, (Fintype.card (FreeColumn P r) - n / 2) := by sorry

-- Prove2me | Theorems.Thm_LatinQuarter_mem_completions
-- name    : LatinQuarter.mem_completions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:23.721918+00:00
-- url     : https://prove2.me/theorems/d151c1bd-e7fd-41a7-abee-a0bd766fd89d
-- title:
--   Latin Quarter: mem completions
-- statement:
--   The Latin Quarter construction uses the mem completions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Basic.lean#L46-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Basic.lean#L46-L50

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_LatinQuarter_Basic
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter

theorem LatinQuarter.mem_completions {n : ℕ} {P : Finset (Cell n)}
    {L M : Square n} :
    M ∈ completions P L ↔ IsLatin M ∧ Agrees P L M := by sorry

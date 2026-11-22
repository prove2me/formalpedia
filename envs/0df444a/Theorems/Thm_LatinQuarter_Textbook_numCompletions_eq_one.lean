-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_numCompletions_eq_one
-- name    : LatinQuarter.Textbook.numCompletions_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:23:28.295787+00:00
-- url     : https://prove2.me/theorems/d5fc2f1e-3b26-4bc4-b87e-a0e3c6e735dd
-- title:
--   Textbook: num Completions eq one
-- statement:
--   The Textbook construction uses the num Completions eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L116-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L116-L121

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.numCompletions_eq_one {n : ℕ} {L : Fin n → Fin n → Fin n}
    {T : Finset (Fin n × Fin n × Fin n)} (h : DefiningSet L T) :
    numCompletions T = 1 := by sorry

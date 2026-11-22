-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_numCompletions_eq
-- name    : LatinQuarter.Textbook.numCompletions_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:23:28.461097+00:00
-- url     : https://prove2.me/theorems/4bd99273-72a9-4ebc-84e7-071e8396948e
-- title:
--   Textbook: num Completions eq
-- statement:
--   The Textbook construction uses the num Completions eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L109-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L109-L114

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.numCompletions_eq {n : ℕ} {T : Finset (Fin n × Fin n × Fin n)}
    {L : Fin n → Fin n → Fin n} (hL : Completes T L) :
    numCompletions T = (completions (T.image fun t => (t.1, t.2.1)) L).card := by sorry

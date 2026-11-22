-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_definingSet_card
-- name    : LatinQuarter.Textbook.definingSet_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:23:26.284188+00:00
-- url     : https://prove2.me/theorems/939b36f1-b8b9-4606-9b36-dc1339bfe934
-- title:
--   Textbook: defining Set card
-- statement:
--   Since `1` is odd, Theorem A gives the lower bound: every defining set of
--   every Latin square of order `n` has at least `⌊n²/4⌋` filled cells.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L141-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L141-L147

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.definingSet_card {n : ℕ} {L : Fin n → Fin n → Fin n}
    {T : Finset (Fin n × Fin n × Fin n)} (h : DefiningSet L T) :
    n * n / 4 ≤ T.card := by sorry

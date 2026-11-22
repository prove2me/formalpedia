-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_completions_even
-- name    : LatinQuarter.Textbook.completions_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:23:34.948349+00:00
-- url     : https://prove2.me/theorems/3d066f4f-1893-4745-80f6-3a8c7d0574f6
-- title:
--   Textbook: completions even
-- statement:
--   **Theorem A.** A set of fewer than `⌊n²/4⌋` filled cells has an even
--   number of completions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L127-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L127-L137

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.completions_even {n : ℕ} (T : Finset (Fin n × Fin n × Fin n))
    (hT : T.card < n * n / 4) : Even (numCompletions T) := by sorry

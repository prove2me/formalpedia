-- Prove2me | Theorems.Thm_LatinQuarter_defining_iff_completions_eq_singleton
-- name    : LatinQuarter.defining_iff_completions_eq_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:26.656916+00:00
-- url     : https://prove2.me/theorems/16985246-cba6-4a49-9f7c-620741630967
-- title:
--   Latin Quarter: defining iff completions eq singleton
-- statement:
--   The Latin Quarter construction uses the defining iff completions eq singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Basic.lean#L52-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Basic.lean#L52-L70

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_LatinQuarter_Basic
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter

theorem LatinQuarter.defining_iff_completions_eq_singleton {n : ℕ}
    (P : Finset (Cell n)) (L : Square n) :
    IsDefining P L ↔ completions P L = {L} := by sorry

-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_completes_iff
-- name    : LatinQuarter.Textbook.completes_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:23:26.371185+00:00
-- url     : https://prove2.me/theorems/9a5b7106-e378-4161-9da0-471471a5fd70
-- title:
--   Textbook: completes iff
-- statement:
--   Once `L` completes `T`, the completions of `T` are the Latin squares that
--   agree with `L` on the cells of `T`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L95-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L95-L107

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.completes_iff {n : ℕ} {T : Finset (Fin n × Fin n × Fin n)}
    {L : Fin n → Fin n → Fin n} (hL : Completes T L) (M : Fin n → Fin n → Fin n) :
    Completes T M ↔ IsLatin M ∧ Agrees (T.image fun t => (t.1, t.2.1)) L M := by sorry

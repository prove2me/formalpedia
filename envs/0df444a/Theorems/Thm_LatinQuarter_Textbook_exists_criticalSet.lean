-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_exists_criticalSet
-- name    : LatinQuarter.Textbook.exists_criticalSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:23:39.858966+00:00
-- url     : https://prove2.me/theorems/450900c2-4832-486e-b0ab-2a8af9062aec
-- title:
--   Textbook: exists critical Set
-- statement:
--   Every Latin square has a critical set: start from all `n²` filled cells.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L176-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L176-L189

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.exists_criticalSet {n : ℕ} {L : Fin n → Fin n → Fin n} (hL : Latin L) :
    ∃ T, CriticalSet L T := by sorry

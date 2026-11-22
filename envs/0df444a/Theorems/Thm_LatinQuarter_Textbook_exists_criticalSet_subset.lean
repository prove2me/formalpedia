-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_exists_criticalSet_subset
-- name    : LatinQuarter.Textbook.exists_criticalSet_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:23:37.225074+00:00
-- url     : https://prove2.me/theorems/c1cdb96f-f1b1-4996-b1a2-0814ae8c35c1
-- title:
--   Textbook: exists critical Set subset
-- statement:
--   Emptying filled cells one at a time while the completion stays unique ends
--   at a critical set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L153-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L153-L173

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.exists_criticalSet_subset {n : ℕ} {L : Fin n → Fin n → Fin n} :
    ∀ (k : ℕ) (T : Finset (Fin n × Fin n × Fin n)), T.card = k →
      DefiningSet L T → ∃ T' ⊆ T, CriticalSet L T' := by sorry

-- Prove2me | Theorems.Thm_NemytskiiLebesgue_ennreal_holderTriple_of_lt_of_lt
-- name    : NemytskiiLebesgue.ennreal_holderTriple_of_lt_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:54.281754+00:00
-- url     : https://prove2.me/theorems/467fea0a-aacf-404f-b13c-e9f36630f76f
-- title:
--   Nemytskii Lebesgue: ennreal holder Triple of lt of lt
-- statement:
--   The Nemytskii Lebesgue construction uses the ennreal holder Triple of lt of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L104-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L104-L116

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal

theorem NemytskiiLebesgue.ennreal_holderTriple_of_lt_of_lt
    {p α : ℝ} (hp : 0 < p) (hα : 0 < α) :
    ENNReal.HolderTriple ↱(p / α) ↱p ↱(p / (α + 1)) := by sorry

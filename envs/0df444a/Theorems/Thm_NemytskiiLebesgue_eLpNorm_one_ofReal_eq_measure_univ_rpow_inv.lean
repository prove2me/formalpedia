-- Prove2me | Theorems.Thm_NemytskiiLebesgue_eLpNorm_one_ofReal_eq_measure_univ_rpow_inv
-- name    : NemytskiiLebesgue.eLpNorm_one_ofReal_eq_measure_univ_rpow_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:56.729793+00:00
-- url     : https://prove2.me/theorems/d55b20bb-9ddf-4762-bd42-80b83905c6a5
-- title:
--   Nemytskii Lebesgue: e Lp Norm one of Real eq measure univ rpow inv
-- statement:
--   The Nemytskii Lebesgue construction uses the e Lp Norm one of Real eq measure univ rpow inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L132-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Lipschitz.lean#L132-L139

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

theorem NemytskiiLebesgue.eLpNorm_one_ofReal_eq_measure_univ_rpow_inv
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p α : ℝ} (hp : 0 < p) (hα : 0 < α) :
    eLpNorm ↓(1 : ℝ) ↱(p / α) μ = (μ ⊤) ^ (α / p) := by sorry

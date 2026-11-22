-- Prove2me | Theorems.Thm_MeasureTheory_Measure_nnreal_smul_real_apply
-- name    : MeasureTheory.Measure.nnreal_smul_real_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:30:28.172835+00:00
-- url     : https://prove2.me/theorems/d98274d9-2351-4eb7-81b6-d9ce76f93dd4
-- title:
--   Measure: nnreal smul real apply
-- statement:
--   The Measure construction uses the nnreal smul real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean#L33-L35
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean#L33-L35

module
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
set_option autoImplicit true
@[expose] public section
public section
open Function Set
open scoped ENNReal NNReal
open MeasureTheory
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}

theorem MeasureTheory.Measure.nnreal_smul_real_apply
    (c : ℝ≥0) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c • μ.real s := by sorry

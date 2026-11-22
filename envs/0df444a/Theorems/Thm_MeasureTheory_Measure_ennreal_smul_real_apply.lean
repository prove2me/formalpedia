-- Prove2me | Theorems.Thm_MeasureTheory_Measure_ennreal_smul_real_apply
-- name    : MeasureTheory.Measure.ennreal_smul_real_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:23:16.790801+00:00
-- url     : https://prove2.me/theorems/ede9df88-1297-4ac8-96c1-ff7a53fe7266
-- title:
--   Measure: ennreal smul real apply
-- statement:
--   The Measure construction uses the ennreal smul real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean#L29-L31
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean#L29-L31

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

theorem MeasureTheory.Measure.ennreal_smul_real_apply
    (c : ℝ≥0∞) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c.toReal • μ.real s := by sorry

-- Prove2me | Theorems.Thm_MeasureTheory_Measure_prod_real_singleton
-- name    : MeasureTheory.Measure.prod_real_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:49.255659+00:00
-- url     : https://prove2.me/theorems/c275ab6f-e040-4971-b859-40565601ba20
-- title:
--   Measure: prod real singleton
-- statement:
--   The Measure construction uses the prod real singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean#L43-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean#L43-L47

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

theorem MeasureTheory.Measure.prod_real_singleton
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x :
  α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by sorry

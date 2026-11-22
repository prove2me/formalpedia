-- Prove2me | Theorems.Thm_MeasureTheory_measureReal_preimage_fst_singleton_eq_sum
-- name    : MeasureTheory.measureReal_preimage_fst_singleton_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:46.840881+00:00
-- url     : https://prove2.me/theorems/b8161ac3-c954-404b-87a6-d0f69d38430c
-- title:
--   Measure Theory: measure Real preimage fst singleton eq sum
-- statement:
--   The Measure Theory construction uses the measure Real preimage fst singleton eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean#L51-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean#L51-L56

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
variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ω']

theorem MeasureTheory.measureReal_preimage_fst_singleton_eq_sum [Fintype Ω'] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (x : Ω) :
    μ.real (Prod.fst ⁻¹' {x}) = ∑ y : Ω', μ.real {(x, y)} := by sorry

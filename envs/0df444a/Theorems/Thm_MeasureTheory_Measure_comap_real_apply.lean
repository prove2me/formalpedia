-- Prove2me | Theorems.Thm_MeasureTheory_Measure_comap_real_apply
-- name    : MeasureTheory.Measure.comap_real_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:25:13.643277+00:00
-- url     : https://prove2.me/theorems/88c454c3-fd07-4f78-8762-1c80f07af360
-- title:
--   Measure: comap real apply
-- statement:
--   The Measure construction uses the comap real apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean#L37-L41
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Real.lean#L37-L41

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

theorem MeasureTheory.Measure.comap_real_apply {s : Set α} {f : α → β} (hfi : Injective f)
    (hf : ∀ s,
      MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    (Measure.comap f μ).real s = μ.real (f '' s) := by sorry

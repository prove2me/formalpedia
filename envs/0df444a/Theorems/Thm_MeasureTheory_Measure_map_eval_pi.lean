-- Prove2me | Theorems.Thm_MeasureTheory_Measure_map_eval_pi
-- name    : MeasureTheory.Measure.map_eval_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:25:28.260798+00:00
-- url     : https://prove2.me/theorems/b6a4a8d4-9310-4fcd-bf2c-41ceee931a46
-- title:
--   Measure: map eval pi
-- statement:
--   The Measure construction uses the map eval pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Constructions/Pi.lean#L44-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Constructions/Pi.lean#L44-L46

module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
set_option autoImplicit true
@[expose] public section
public section
open Function Set
open MeasureTheory MeasureTheory.Measure
variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem MeasureTheory.Measure.map_eval_pi (i : ι) : Measure.map (eval i) (Measure.pi μ) = μ i := by sorry

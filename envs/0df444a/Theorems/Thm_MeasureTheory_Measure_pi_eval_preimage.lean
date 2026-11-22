-- Prove2me | Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
-- name    : MeasureTheory.Measure.pi_eval_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:17.880866+00:00
-- url     : https://prove2.me/theorems/804a1d97-11ac-45d0-8c8d-00054dd1ba5d
-- title:
--   Measure: pi eval preimage
-- statement:
--   The Measure construction uses the pi eval preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Constructions/Pi.lean#L38-L42
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Constructions/Pi.lean#L38-L42

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

theorem MeasureTheory.Measure.pi_eval_preimage (i : ι) (s : Set (α i)) :
    Measure.pi μ (eval i ⁻¹' s) = μ i s := by sorry

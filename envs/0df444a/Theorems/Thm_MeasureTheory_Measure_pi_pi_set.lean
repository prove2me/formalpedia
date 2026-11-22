-- Prove2me | Theorems.Thm_MeasureTheory_Measure_pi_pi_set
-- name    : MeasureTheory.Measure.pi_pi_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:19.242605+00:00
-- url     : https://prove2.me/theorems/21a4875c-0a62-4b43-b33d-3c1e0d39d0ac
-- title:
--   Measure: pi pi set
-- statement:
--   The Measure construction uses the pi pi set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Constructions/Pi.lean#L30-L35
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Constructions/Pi.lean#L30-L35

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

theorem MeasureTheory.Measure.pi_pi_set (t : Set ι) [DecidablePred (· ∈ t)] (s : ∀ i, Set (α i)) :
    Measure.pi μ (pi t s) = ∏ i ∈ Finset.univ.filter (· ∈ t), μ i (s i) := by sorry

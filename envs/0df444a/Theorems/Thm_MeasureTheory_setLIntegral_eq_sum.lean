-- Prove2me | Theorems.Thm_MeasureTheory_setLIntegral_eq_sum
-- name    : MeasureTheory.setLIntegral_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:24:51.146731+00:00
-- url     : https://prove2.me/theorems/e78f7b8a-47b1-43ad-b247-9799064967c1
-- title:
--   Measure Theory: set LIntegral eq sum
-- statement:
--   The Measure Theory construction uses the set LIntegral eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean#L37-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean#L37-L39

module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
set_option autoImplicit true
@[expose] public section
public section
open ENNReal
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
variable [MeasurableSingletonClass α]

theorem MeasureTheory.setLIntegral_eq_sum (μ : Measure α) (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x ∈ s, μ {x} * f x := by sorry

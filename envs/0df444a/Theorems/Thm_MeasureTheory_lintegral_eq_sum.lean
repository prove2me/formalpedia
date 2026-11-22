-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_eq_sum
-- name    : MeasureTheory.lintegral_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:30:00.929931+00:00
-- url     : https://prove2.me/theorems/1fca2318-aff5-4617-af63-16c29f6b20d7
-- title:
--   Measure Theory: lintegral eq sum
-- statement:
--   The Measure Theory construction uses the lintegral eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean#L28-L30
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean#L28-L30

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

theorem MeasureTheory.lintegral_eq_sum (μ : Measure α) (f : α → ℝ≥0∞) [Fintype α] :
    ∫⁻ x, f x ∂μ = ∑ x, μ {x} * f x := by sorry

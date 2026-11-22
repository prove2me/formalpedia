-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_eq_tsum
-- name    : MeasureTheory.lintegral_eq_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:24.754959+00:00
-- url     : https://prove2.me/theorems/7c0f5121-2613-487b-ac7e-1e46696efdc1
-- title:
--   Measure Theory: lintegral eq tsum
-- statement:
--   The Measure Theory construction uses the lintegral eq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean#L32-L34
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean#L32-L34

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

theorem MeasureTheory.lintegral_eq_tsum (μ : Measure α) (f : α → ℝ≥0∞) [Countable α] :
    ∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x := by sorry

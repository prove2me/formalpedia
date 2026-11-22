-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_eq_setLIntegral
-- name    : MeasureTheory.lintegral_eq_setLIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:24:50.6454+00:00
-- url     : https://prove2.me/theorems/3551fd8f-a5bf-484f-b148-556c447b33bf
-- title:
--   Measure Theory: lintegral eq set LIntegral
-- statement:
--   The Measure Theory construction uses the lintegral eq set LIntegral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean#L31-L33
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean#L31-L33

module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
set_option autoImplicit true
@[expose] public section
public section
open ENNReal
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

theorem MeasureTheory.lintegral_eq_setLIntegral (hs : μ sᶜ = 0) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ x in s, f x ∂μ := by sorry

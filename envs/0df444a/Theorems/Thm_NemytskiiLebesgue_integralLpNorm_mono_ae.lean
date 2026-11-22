-- Prove2me | Theorems.Thm_NemytskiiLebesgue_integralLpNorm_mono_ae
-- name    : NemytskiiLebesgue.integralLpNorm_mono_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:14.66249+00:00
-- url     : https://prove2.me/theorems/2adbf06a-fc40-4652-9b9e-4b24218d2fab
-- title:
--   Nemytskii Lebesgue: integral Lp Norm mono ae
-- statement:
--   The Nemytskii Lebesgue construction uses the integral Lp Norm mono ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L51-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L51-L61

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.Have
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal

theorem NemytskiiLebesgue.integralLpNorm_mono_ae {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : Ω → E} {g : Ω → F} {p : ℝ≥0∞} {μ : Measure Ω}
    (hfg : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ ‖g ω‖) : integralLpNorm f p μ ≤ integralLpNorm g p μ := by sorry

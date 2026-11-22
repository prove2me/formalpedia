-- Prove2me | Theorems.Thm_NemytskiiLebesgue_integralLpNorm_eq_lintegral_rpow_enorm_toReal
-- name    : NemytskiiLebesgue.integralLpNorm_eq_lintegral_rpow_enorm_toReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:12.293919+00:00
-- url     : https://prove2.me/theorems/f6bf2aa2-eda5-4168-8e63-e76a95d28f1b
-- title:
--   Nemytskii Lebesgue: integral Lp Norm eq lintegral rpow enorm to Real
-- statement:
--   The Nemytskii Lebesgue construction uses the integral Lp Norm eq lintegral rpow enorm to Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L45-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L45-L49

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

theorem NemytskiiLebesgue.integralLpNorm_eq_lintegral_rpow_enorm_toReal {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {f : Ω → E} {p : ℝ≥0∞} {μ : Measure Ω}
    (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    integralLpNorm f p μ = (∫⁻ ω, ‖f ω‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by sorry

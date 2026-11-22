-- Prove2me | Theorems.Thm_NemytskiiLebesgue_integralLpNorm_le_eLpNorm_of_ae_le
-- name    : NemytskiiLebesgue.integralLpNorm_le_eLpNorm_of_ae_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:08.844694+00:00
-- url     : https://prove2.me/theorems/0c052fc2-d3b2-4ffe-80d6-9ce4d0cb4bc6
-- title:
--   Nemytskii Lebesgue: integral Lp Norm le e Lp Norm of ae le
-- statement:
--   The Nemytskii Lebesgue construction uses the integral Lp Norm le e Lp Norm of ae le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L63-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L63-L68

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

theorem NemytskiiLebesgue.integralLpNorm_le_eLpNorm_of_ae_le {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : Ω → E} {g : Ω → F} {p : ℝ≥0∞} {μ : Measure Ω}
    (hg : AEStronglyMeasurable g μ) (hfg : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ ‖g ω‖) :
    integralLpNorm f p μ ≤ eLpNorm g p μ := by sorry

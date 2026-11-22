-- Prove2me | Theorems.Thm_NemytskiiLebesgue_integralLpNorm_eq_eLpNorm
-- name    : NemytskiiLebesgue.integralLpNorm_eq_eLpNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:13.101178+00:00
-- url     : https://prove2.me/theorems/a43a5ad7-f1a9-46e5-9bae-2fd7b8b4408d
-- title:
--   Nemytskii Lebesgue: integral Lp Norm eq e Lp Norm
-- statement:
--   The Nemytskii Lebesgue construction uses the integral Lp Norm eq e Lp Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L40-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L40-L43

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

theorem NemytskiiLebesgue.integralLpNorm_eq_eLpNorm {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {f : Ω → E} {p : ℝ≥0∞} {μ : Measure Ω}
    (hf : AEStronglyMeasurable f μ) : integralLpNorm f p μ = eLpNorm f p μ := by sorry

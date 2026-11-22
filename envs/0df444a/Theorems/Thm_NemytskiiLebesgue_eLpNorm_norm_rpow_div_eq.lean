-- Prove2me | Theorems.Thm_NemytskiiLebesgue_eLpNorm_norm_rpow_div_eq
-- name    : NemytskiiLebesgue.eLpNorm_norm_rpow_div_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:13.102692+00:00
-- url     : https://prove2.me/theorems/c254ed0a-c144-4437-bc8d-79cbf019f123
-- title:
--   Nemytskii Lebesgue: e Lp Norm norm rpow div eq
-- statement:
--   The Nemytskii Lebesgue construction uses the e Lp Norm norm rpow div eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L178-L185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L178-L185

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
open scoped ENNReal
open scoped RealInnerProductSpace
open MeasureTheory

theorem NemytskiiLebesgue.eLpNorm_norm_rpow_div_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D] (u : Ω → D)
    (hu : AEStronglyMeasurable u μ) {p α : ℝ} (hα : 0 < α) (hp : 0 < p) :
    eLpNorm (‖u ·‖ ^ α) ↱(p / α) μ = (eLpNorm u ↱p μ) ^ α := by sorry

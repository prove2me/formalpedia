-- Prove2me | Theorems.Thm_NemytskiiLebesgue_memLp_rpow_div_of_memLp_of_ae_nonneg
-- name    : NemytskiiLebesgue.memLp_rpow_div_of_memLp_of_ae_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:15.475408+00:00
-- url     : https://prove2.me/theorems/49782a3b-412f-495c-b0a1-5051da8c994f
-- title:
--   Nemytskii Lebesgue: mem Lp rpow div of mem Lp of ae nonneg
-- statement:
--   The Nemytskii Lebesgue construction uses the mem Lp rpow div of mem Lp of ae nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L206-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L206-L213

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

theorem NemytskiiLebesgue.memLp_rpow_div_of_memLp_of_ae_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {α : ℝ} (hα : 0 < α)
    {v : Ω → ℝ} (h0v : 0 ≤ᵐ[μ] v) {p : ℝ} (hvp : MemLp v ↱p μ) :
    MemLp (v · ^ α) ↱(p / α) μ := by sorry

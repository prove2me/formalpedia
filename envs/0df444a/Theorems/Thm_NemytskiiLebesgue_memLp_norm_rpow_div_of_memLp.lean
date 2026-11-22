-- Prove2me | Theorems.Thm_NemytskiiLebesgue_memLp_norm_rpow_div_of_memLp
-- name    : NemytskiiLebesgue.memLp_norm_rpow_div_of_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:11.590194+00:00
-- url     : https://prove2.me/theorems/06eaf63d-ac79-4205-a778-953939071c48
-- title:
--   Nemytskii Lebesgue: mem Lp norm rpow div of mem Lp
-- statement:
--   The Nemytskii Lebesgue construction uses the mem Lp norm rpow div of mem Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L196-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L196-L204

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

theorem NemytskiiLebesgue.memLp_norm_rpow_div_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {α : ℝ} (hα : 0 < α)
    {u : Ω → E} {p : ℝ} (hup : MemLp u ↱p μ) :
    MemLp (‖u ·‖ ^ α) ↱(p / α) μ := by sorry

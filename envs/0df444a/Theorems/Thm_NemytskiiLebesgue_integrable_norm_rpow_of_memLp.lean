-- Prove2me | Theorems.Thm_NemytskiiLebesgue_integrable_norm_rpow_of_memLp
-- name    : NemytskiiLebesgue.integrable_norm_rpow_of_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:18.462076+00:00
-- url     : https://prove2.me/theorems/d0db403f-d905-4b82-8748-439b5990b838
-- title:
--   Nemytskii Lebesgue: integrable norm rpow of mem Lp
-- statement:
--   The Nemytskii Lebesgue construction uses the integrable norm rpow of mem Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L187-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L187-L194

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

theorem NemytskiiLebesgue.integrable_norm_rpow_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ} (hp : 1 < p)
    {u : Ω → E} (hup : MemLp u ↱p μ) :
    Integrable (‖u ·‖ ^ p) μ := by sorry

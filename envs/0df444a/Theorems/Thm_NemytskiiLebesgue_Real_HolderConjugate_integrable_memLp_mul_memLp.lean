-- Prove2me | Theorems.Thm_NemytskiiLebesgue_Real_HolderConjugate_integrable_memLp_mul_memLp
-- name    : NemytskiiLebesgue.Real.HolderConjugate.integrable_memLp_mul_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:13.653091+00:00
-- url     : https://prove2.me/theorems/5fc3369f-2e91-4996-86bf-00c2a5bce956
-- title:
--   Holder Conjugate: integrable mem Lp mul mem Lp
-- statement:
--   The Holder Conjugate construction uses the integrable mem Lp mul mem Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L215-L222
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L215-L222

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

theorem NemytskiiLebesgue.Real.HolderConjugate.integrable_memLp_mul_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {g : Ω → ℝ} (hgq : MemLp g ↱q μ)
    {l : Ω → ℝ} (hlp : MemLp l ↱p μ) :
    Integrable (fun ω : Ω => g ω * l ω) μ := by sorry

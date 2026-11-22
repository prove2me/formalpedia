-- Prove2me | Theorems.Thm_NemytskiiLebesgue_Real_HolderConjugate_integrable_memLp_inner_memLp
-- name    : NemytskiiLebesgue.Real.HolderConjugate.integrable_memLp_inner_memLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:09.651457+00:00
-- url     : https://prove2.me/theorems/27d26ced-db04-4c83-9c27-067369277e11
-- title:
--   Holder Conjugate: integrable mem Lp inner mem Lp
-- statement:
--   The Holder Conjugate construction uses the integrable mem Lp inner mem Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L224-L235
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L224-L235

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

theorem NemytskiiLebesgue.Real.HolderConjugate.integrable_memLp_inner_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {g : Ω → E} (hgq : MemLp g ↱q μ)
    {l : Ω → E} (hlp : MemLp l ↱p μ) :
    Integrable (fun ω : Ω => ⟪g ω, l ω⟫) μ := by sorry

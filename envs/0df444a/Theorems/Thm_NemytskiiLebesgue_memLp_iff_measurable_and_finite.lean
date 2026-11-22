-- Prove2me | Theorems.Thm_NemytskiiLebesgue_memLp_iff_measurable_and_finite
-- name    : NemytskiiLebesgue.memLp_iff_measurable_and_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:12.429977+00:00
-- url     : https://prove2.me/theorems/a61b8915-bd90-4c11-9639-c7b0925970c1
-- title:
--   Nemytskii Lebesgue: mem Lp iff measurable and finite
-- statement:
--   The Nemytskii Lebesgue construction uses the mem Lp iff measurable and finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L165-L169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L165-L169

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

theorem NemytskiiLebesgue.memLp_iff_measurable_and_finite
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [ENorm E]
    {μ : Measure Ω} {p : ℝ≥0∞} {f : Ω → E} :
    MemLp f p μ ↔ AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ⊤ := by sorry

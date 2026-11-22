-- Prove2me | Theorems.Thm_NemytskiiLebesgue_natCast_div_natCast_eq_ofReal
-- name    : NemytskiiLebesgue.natCast_div_natCast_eq_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:35.980771+00:00
-- url     : https://prove2.me/theorems/fe03d5d5-7989-46fa-896f-71f41decf7c4
-- title:
--   Nemytskii Lebesgue: nat Cast div nat Cast eq of Real
-- statement:
--   The Nemytskii Lebesgue construction uses the nat Cast div nat Cast eq of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L98-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L98-L102

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

theorem NemytskiiLebesgue.natCast_div_natCast_eq_ofReal (p : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (p : ℝ≥0∞) / (q : ℝ≥0∞) = ↱((p : ℝ) / (q : ℝ)) := by sorry

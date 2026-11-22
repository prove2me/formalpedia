-- Prove2me | Theorems.Thm_NemytskiiLebesgue_rpow_le_ofReal_rpow_of_le_ofReal
-- name    : NemytskiiLebesgue.rpow_le_ofReal_rpow_of_le_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:15.916706+00:00
-- url     : https://prove2.me/theorems/10af5e3c-1466-4dc7-97df-1ff1d2375944
-- title:
--   Nemytskii Lebesgue: rpow le of Real rpow of le of Real
-- statement:
--   The Nemytskii Lebesgue construction uses the rpow le of Real rpow of le of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L108-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L108-L113

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

theorem NemytskiiLebesgue.rpow_le_ofReal_rpow_of_le_ofReal
    {α R : ℝ} (hα : 0 ≤ α) (hR : 0 < R)
    {x : ℝ≥0∞} (hx : x ≤ ↱R) :
    x ^ α ≤ ↱(R ^ α) := by sorry

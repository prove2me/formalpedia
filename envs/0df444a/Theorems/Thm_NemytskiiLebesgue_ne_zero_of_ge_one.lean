-- Prove2me | Theorems.Thm_NemytskiiLebesgue_ne_zero_of_ge_one
-- name    : NemytskiiLebesgue.ne_zero_of_ge_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:09.806179+00:00
-- url     : https://prove2.me/theorems/f5f56c90-64e3-478c-8558-bc2ee71f359e
-- title:
--   Nemytskii Lebesgue: ne zero of ge one
-- statement:
--   The Nemytskii Lebesgue construction uses the ne zero of ge one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L81-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L81-L86

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

theorem NemytskiiLebesgue.ne_zero_of_ge_one {α : Type*} [Zero α] [One α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1
  : α)]
    {x : α} (h1x : 1 ≤ x) : x ≠ 0 := by sorry

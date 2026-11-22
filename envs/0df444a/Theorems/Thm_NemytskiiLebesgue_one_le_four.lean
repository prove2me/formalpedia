-- Prove2me | Theorems.Thm_NemytskiiLebesgue_one_le_four
-- name    : NemytskiiLebesgue.one_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:18.829411+00:00
-- url     : https://prove2.me/theorems/40f1d4a6-6255-4f6e-97a2-fc36635f9d25
-- title:
--   Nemytskii Lebesgue: one le four
-- statement:
--   The Nemytskii Lebesgue construction uses the one le four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L70-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L70-L76

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

theorem NemytskiiLebesgue.one_le_four {α : Type*} [AddCommMonoidWithOne α] [Preorder α] [ZeroLEOneClass α] [AddLeftMono
  α] :
    (1 : α) ≤ (4 : α) := by sorry

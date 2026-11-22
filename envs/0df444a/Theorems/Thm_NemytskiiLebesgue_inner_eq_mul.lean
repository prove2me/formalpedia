-- Prove2me | Theorems.Thm_NemytskiiLebesgue_inner_eq_mul
-- name    : NemytskiiLebesgue.inner_eq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:16.688493+00:00
-- url     : https://prove2.me/theorems/66f0f9e1-555c-4d21-ac29-4811f27c2357
-- title:
--   Nemytskii Lebesgue: inner eq mul
-- statement:
--   The Nemytskii Lebesgue construction uses the inner eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L159-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L159-L161

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

theorem NemytskiiLebesgue.inner_eq_mul (a b : ℝ) : ⟪a, b⟫ = a * b := by sorry

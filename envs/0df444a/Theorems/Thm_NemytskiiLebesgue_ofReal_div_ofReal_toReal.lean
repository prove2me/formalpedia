-- Prove2me | Theorems.Thm_NemytskiiLebesgue_ofReal_div_ofReal_toReal
-- name    : NemytskiiLebesgue.ofReal_div_ofReal_toReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:13.9556+00:00
-- url     : https://prove2.me/theorems/3e1a642d-d424-4f06-bd02-d65e23e5c69d
-- title:
--   Nemytskii Lebesgue: of Real div of Real to Real
-- statement:
--   The Nemytskii Lebesgue construction uses the of Real div of Real to Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L104-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L104-L106

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

theorem NemytskiiLebesgue.ofReal_div_ofReal_toReal {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (↱p / ↱q).toReal = p / q := by sorry

-- Prove2me | Theorems.Thm_NemytskiiLebesgue_pow_transfer_ennreal_ofReal
-- name    : NemytskiiLebesgue.pow_transfer_ennreal_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:13.832673+00:00
-- url     : https://prove2.me/theorems/f953e4b4-ac15-4ba6-8920-ae962392da65
-- title:
--   Nemytskii Lebesgue: pow transfer ennreal of Real
-- statement:
--   The Nemytskii Lebesgue construction uses the pow transfer ennreal of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L115-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L115-L143

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

theorem NemytskiiLebesgue.pow_transfer_ennreal_ofReal
    {a : ℝ} (ha : 0 ≤ a)
    {b : ℝ} (hb : 0 ≤ b)
    {c : ℝ} (hc : 0 < c)
    {d : ℝ} (hd : 0 < d)
    {r : ℝ} (hr : 0 ≤ r)
    (hcarb : c * a ^ r < b) :
    ↱a ^ (d * r) ≤ ↱(c ^ (-d)) * ↱b ^ d := by sorry

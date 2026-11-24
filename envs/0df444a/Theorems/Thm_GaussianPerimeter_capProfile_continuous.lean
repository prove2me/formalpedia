-- Prove2me | Theorems.Thm_GaussianPerimeter_capProfile_continuous
-- name    : GaussianPerimeter.capProfile_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:08:23.201053+00:00
-- url     : https://prove2.me/theorems/d979bbe5-c54a-4d40-b622-02faecd80890
-- title:
--   Gaussian Perimeter: cap Profile continuous
-- statement:
--   The Gaussian Perimeter construction uses the cap Profile continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean#L58-L61
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean#L58-L61

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter

theorem GaussianPerimeter.capProfile_continuous {n : ℕ} (hn : 2 ≤ n) : Continuous (capProfile n) := by sorry

-- Prove2me | Theorems.Thm_GaussianPerimeter_capTail_le
-- name    : GaussianPerimeter.capTail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:26:47.021899+00:00
-- url     : https://prove2.me/theorems/a0f1668f-1b47-4a57-b887-c7eef1411689
-- title:
--   Gaussian Perimeter: cap Tail le
-- statement:
--   Integrating `(u / t) * capProfile n u` gives an upper bound on the cap numerator.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean#L72-L107
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean#L72-L107

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

theorem GaussianPerimeter.capTail_le {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) :
    capTail n t ≤ (1 - t ^ 2) ^ ((n : ℝ) / 2) / ((n : ℝ) * t * capNormalizer n) := by sorry

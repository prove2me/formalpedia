-- Prove2me | Theorems.Thm_GaussianPerimeter_capTail_eq_ballSections
-- name    : GaussianPerimeter.capTail_eq_ballSections
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:32:20.381556+00:00
-- url     : https://prove2.me/theorems/05bf46b8-a199-4e8c-92ee-28640161650f
-- title:
--   Gaussian Perimeter: cap Tail eq ball Sections
-- statement:
--   The exact spherical cap probability in terms of cross-sections of the unit ball.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean#L183-L201
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean#L183-L201

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

theorem GaussianPerimeter.capTail_eq_ballSections {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    capTail n t = (t / ((n : ℝ) + 1) * capProfile (n + 2) t +
      (∫ u in t..1, capProfile (n + 2) u)) / capNormalizer (n + 2) := by sorry

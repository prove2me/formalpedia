-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityLaplaceIntegralValue
-- name    : Kyprianou.Ch01.inverseGaussianDensityLaplaceIntegralValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:06:48.906475+00:00
-- url     : https://prove2.me/theorems/ffb3fe38-f740-41bf-9d66-902bdf632cba
-- title:
--   Exact Laplace integral of inverse Gaussian passage-time density
-- statement:
--   Exact Laplace integral of inverse Gaussian passage-time density. Source exact normalised inverse Gaussian first-passage density s/(sqrt(2πx³)) exp(-(s-bx)²/(2x)) on the positive half-line; this is one independent analytic obligation of the exact density Laplace theorem. The original assumptions s>0 and b>0, with the full q≥0 transform where applicable, are unchanged.
-- source:
--   Kyprianou (2006) Chapter 1, Exercise 1.11, first-passage density of Brownian drift; source-exact analytic decomposition.

import Mathlib
open MeasureTheory Real Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianDensityLaplaceIntegralValue
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    ∀ q : ℝ, 0 ≤ q →
      (∫ x, Real.exp (-q * x) ∂IG) =
        Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b)) := by sorry

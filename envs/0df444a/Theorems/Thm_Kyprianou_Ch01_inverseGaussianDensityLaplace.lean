-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityLaplace
-- name    : Kyprianou.Ch01.inverseGaussianDensityLaplace
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:20:42.187195+00:00
-- url     : https://prove2.me/theorems/f8b1d234-4b0c-4b77-8159-db9841b783a6
-- title:
--   Exercise 1.6(iii): inverse Gaussian first-passage density and Laplace transform
-- statement:
--   Kyprianou Exercise 1.6(iii): the inverse Gaussian first-passage density μ_s(dx)=s/(√(2πx³))exp(−(s−bx)²/(2x))dx on x>0 has unit total mass and Laplace transform exp(−s(√(b²+2q)−b)) for all q≥0. This confirms the full density formula rather than only the passage-time transform. Draft awaiting remote elaboration.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.6(iii), printed p. 29.

import Mathlib
open MeasureTheory Filter Set Real
open scoped NNReal ENNReal Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianDensityLaplace
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    IG Set.univ = 1 ∧
    ∀ q : ℝ, 0 ≤ q →
      Integrable (fun x : ℝ => Real.exp (-q * x)) IG ∧
      (∫ x, Real.exp (-q * x) ∂IG) =
        Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b)) := by
  sorry

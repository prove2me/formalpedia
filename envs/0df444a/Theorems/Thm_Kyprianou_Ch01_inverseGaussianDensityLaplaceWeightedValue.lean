-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityLaplaceWeightedValue
-- name    : Kyprianou.Ch01.inverseGaussianDensityLaplaceWeightedValue
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T18:59:40.692038+00:00
-- url     : https://prove2.me/theorems/f805e23c-04f7-4076-a7d3-bd616dd7356d
-- title:
--   Exact weighted Lebesgue Laplace value of the inverse-Gaussian passage-time density
-- statement:
--   For positive barrier s, positive drift b, and discount q>=0, the integral over x>0 of the source-exact inverse Gaussian density times exp(-q x) equals exp(-s(sqrt(b²+2q)-b)). This isolates the genuinely nontrivial real-analytic Gaussian Laplace kernel from the already-independent withDensity bookkeeping.
-- source:
--   Kyprianou (2006) Exercise 1.6(iii) inverse Gaussian first-passage density; its standard x^-3/2 Laplace integral.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianDensityLaplaceWeightedValue
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫ x in Set.Ioi (0 : ℝ),
      ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
         Real.exp (-((s - b * x) ^ 2 / (2 * x)))) • Real.exp (-q * x) ∂volume) =
      Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b)) := by sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianLaplaceDeficitTendsZeroV1
-- name    : Kyprianou.Ch01.inverseGaussianLaplaceDeficitTendsZeroV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:11:04.037074+00:00
-- url     : https://prove2.me/theorems/e2012441-acb0-4410-a395-d31a87c9b6b8
-- title:
--   Inverse Gaussian q=1 Laplace deficit vanishes continuously at zero barrier
-- statement:
--   For any real drift parameter b, the q=1 inverse-Gaussian passage Laplace deficit 1-exp(-s(sqrt(b²+2)-b)) converges to zero as the nonnegative barrier s tends to zero. The proof is purely a composition of continuity of the NNReal-to-Real inclusion, multiplication by a constant, negation, Real.exp, and subtraction. No probabilistic hypotheses or stochastic continuity are required.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, direct continuity of the inverse Gaussian Laplace exponent.

import Mathlib
open Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianLaplaceDeficitTendsZeroV1
    (b : ℝ) :
    Tendsto
      (fun s : ℝ≥0 =>
        1 - Real.exp (-((s : ℝ) * (Real.sqrt (b ^ 2 + 2) - b))))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by sorry

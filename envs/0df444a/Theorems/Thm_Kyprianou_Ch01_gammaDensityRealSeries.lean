-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaDensityRealSeries
-- name    : Kyprianou.Ch01.gammaDensityRealSeries
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:14:42.583244+00:00
-- url     : https://prove2.me/theorems/7ab29871-03f0-4a3e-8e4f-b42a22c49c6f
-- title:
--   Exponential Taylor series collapses the full gamma arrival-density sum to the constant rate
-- statement:
--   For any positive exponential rate beta and nonnegative spatial argument x, the sum over n >= 0 of the gamma(n+1,beta) density beta^(n+1) x^n exp(-beta x) / n! is exactly beta. Prove by the absolute convergence and Taylor expansion of exp(beta x). This is the density-summation step of Kyprianou Exercise 1.8(iv) and preserves the source rate parameter.
-- source:
--   Kyprianou (2006) Exercise 1.8(iv) worked solution printed pp.304–305

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open Real NormedSpace Filter
open scoped BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaDensityRealSeries
    (beta x : ℝ) (hbeta : 0 < beta) (hx : 0 ≤ x) :
    (∑' n : ℕ, beta ^ (n + 1) * x ^ n *
      Real.exp (-beta * x) / (n.factorial : ℝ)) = beta := by
  sorry

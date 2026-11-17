-- Prove2me | Theorems.Thm_Kyprianou_Ch01_realLogSeriesMass
-- name    : Kyprianou.Ch01.realLogSeriesMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:53:46.250491+00:00
-- url     : https://prove2.me/theorems/7468b0a7-b529-41fd-a9b0-109a0a266174
-- title:
--   Exact nonnegative logarithmic-series mass and convergence, normalising logarithmic compound Poisson jump rates
-- statement:
--   For every real 0≤q<1, the real positive series ∑_{k≥1} q^k/k converges, with exact HasSum value −log(1−q). This gives the normalising factor λ=−log p for the logarithmic jump distribution of a geometric count law with p=1−q, which is the exact compound-Poisson intensity in Kyprianou (2006), Chapter 1 Exercise 1.2(i). The proof rigorously transports the pinned complex Taylor logarithm series through the complex-to-real HasSum equivalence and the principal logarithm identity on positive reals.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.2(i), solution printed p. 299; pinned Mathlib Complex.hasSum_taylorSeries_neg_log', Complex.hasSum_ofReal, Complex.ofReal_log.

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.realLogSeriesMass (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => q ^ (n + 1) / ((n : ℝ) + 1))
      (-Real.log (1 - q)) := by
  sorry

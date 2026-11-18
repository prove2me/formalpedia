-- Prove2me | Theorems.Thm_Kyprianou_Ch01_exponentialRateSurvival
-- name    : Kyprianou.Ch01.exponentialRateSurvival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:26:32.567867+00:00
-- url     : https://prove2.me/theorems/842c3478-7100-4c22-856f-c826716ff4cc
-- title:
--   Survival function of the positive exponential inter-arrival distribution
-- statement:
--   For exponential waiting time with positive rate β, the probability of exceeding a nonnegative threshold z is exp(−β z). This establishes the memoryless waiting-time tail underlying the embedded random walk and ladder-height computations in Chapter 1. It uses the pinned Mathlib exponential distribution CDF and probability complement identities.
-- source:
--   Kyprianou (2006), Chapter 1, compound-Poisson embedded risk random walk and exponential inter-arrivals.

import Mathlib
open MeasureTheory ProbabilityTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.exponentialRateSurvival
    (beta z : ℝ) (hbeta : 0 < beta) (hz : 0 ≤ z) :
    (ProbabilityTheory.expMeasure beta).real (Set.Ioi z) =
      Real.exp (-(beta * z)) := by
  sorry

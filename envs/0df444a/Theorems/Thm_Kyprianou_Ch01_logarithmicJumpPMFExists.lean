-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicJumpPMFExists
-- name    : Kyprianou.Ch01.logarithmicJumpPMFExists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T00:06:54.543696+00:00
-- url     : https://prove2.me/theorems/28c20163-026d-4295-8c27-e69d513d3f90
-- title:
--   The logarithmic jump-series weights define a probability mass function
-- statement:
--   For 0<q<1, there is a probability mass function on the nonnegative integers whose weight at n is q^(n+1)/((n+1)(-log(1-q))). This distribution supplies the strictly positive logarithmic jumps of the compound-Poisson representation of a geometric law in Exercise 1.2(i).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpWeightsENNRealMass
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicJumpPMFExists
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ jump : PMF ℕ, ∀ n : ℕ,
      jump n = ENNReal.ofReal
        ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q))) := by
  sorry

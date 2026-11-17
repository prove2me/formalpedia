-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicJumpCharExponent
-- name    : Kyprianou.Ch01.logarithmicJumpCharExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:32:21.131375+00:00
-- url     : https://prove2.me/theorems/abe88a6c-6c97-4fc0-be0f-56018b2369df
-- title:
--   Characteristic exponent of the real logarithmic jump law equals the geometric Lévy exponent
-- statement:
--   For the logarithmic-series probability mass function with q strictly between zero and one, the compound-Poisson rate −log(1−q) times the jump characteristic-function increment equals log(1−q)−log(1−q exp(iξ)) at every real Fourier frequency. This exact distributional identity is the principal analytic step in proving Kyprianou's strict geometric compound-Poisson representation.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i), compound-Poisson representation of the geometric count law.

import Mathlib
open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicJumpCharExponent
    (q xi : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (jump : PMF ℕ)
    (hjump : ∀ n : ℕ, jump n = ENNReal.ofReal
      ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q)))) :
    (((-Real.log (1 - q) : ℝ) : ℂ) *
      (charFun (jump.toMeasure.map
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) xi - 1)) =
      Complex.log (1 - (q : ℂ)) -
        Complex.log (1 - (q : ℂ) *
          Complex.exp ((xi : ℂ) * Complex.I)) := by
  sorry

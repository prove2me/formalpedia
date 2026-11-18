-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicWeightedProbabilityMeasureSumFinite
-- name    : Kyprianou.Ch01.logarithmicWeightedProbabilityMeasureSumFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:11:09.771209+00:00
-- url     : https://prove2.me/theorems/2d86e6bc-9a40-462b-b11c-b765800f08bc
-- title:
--   Summable logarithmic cluster weights induce a finite intensity on arbitrary probability mark laws
-- statement:
--   For 0≤q<1 and any indexed family of real probability measures, the sum of measures weighted by q^(n+1)/(n+1) has finite total mass. This proves the finiteness of the logarithmic convolution cluster intensity for the strict geometric stopped random sum, before removing the mass at zero.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), logarithmic compound-Poisson cluster weights.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_realLogSeriesMass
open MeasureTheory
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicWeightedProbabilityMeasureSumFinite
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ν : ℕ → Measure ℝ)
    (hν : ∀ n : ℕ, IsProbabilityMeasure (ν n)) :
    (Measure.sum fun n : ℕ =>
      (ENNReal.ofReal (q ^ (n + 1) / (n + 1 : ℝ))) • ν n)
      Set.univ < ⊤ := by
  sorry

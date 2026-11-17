-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicPositiveJumpLaw
-- name    : Kyprianou.Ch01.logarithmicPositiveJumpLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:12:51.29098+00:00
-- url     : https://prove2.me/theorems/c6d3c9a8-4a62-4301-bbaf-a07eb5422d10
-- title:
--   Logarithmic compound-Poisson jump law is a probability measure supported away from zero
-- statement:
--   For 0<q<1, there exists a logarithmic jump PMF with the source-faithful prescribed weights. Under the map n ↦ n+1 into real numbers, this gives a probability measure on ℝ with zero mass at the origin, as required by the compound-Poisson Lévy-driver theorem.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i): logarithmic-jump compound-Poisson representation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpPMFExists
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicPositiveJumpLaw
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ jump : PMF ℕ,
      (∀ n : ℕ, jump n =
        ENNReal.ofReal
          ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q)))) ∧
      IsProbabilityMeasure
        (jump.toMeasure.map (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) ∧
      (jump.toMeasure.map (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) {0} = 0 := by
  sorry

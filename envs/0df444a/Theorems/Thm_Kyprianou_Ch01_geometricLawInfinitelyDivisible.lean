-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricLawInfinitelyDivisible
-- name    : Kyprianou.Ch01.geometricLawInfinitelyDivisible
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:18:37.483427+00:00
-- url     : https://prove2.me/theorems/0f4491ed-975b-423d-a4dc-1b8cc170f745
-- title:
--   Exercise 1.2(i): geometric counting law is infinitely divisible
-- statement:
--   Geometric random variable Γ_p on {0,1,2,...} with mass p(1−p)^k for 0<p≤1 has an infinitely divisible law, as required by the first part of Exercise 1.2. The geometric distribution is defined by its atom masses, and the conclusion requires all convolution roots. Draft has not been remotely elaborated.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i), printed pp. 26–27.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricLawInfinitelyDivisible
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (G : Measure ℕ) [IsProbabilityMeasure G]
    (hGeom : ∀ k : ℕ,
      G {k} = ENNReal.ofReal (p * (1 - p) ^ k)) :
    LevyFoundations.isInfinitelyDivisibleLaw
      (G.map (fun k : ℕ => (k : ℝ))) := by
  sorry

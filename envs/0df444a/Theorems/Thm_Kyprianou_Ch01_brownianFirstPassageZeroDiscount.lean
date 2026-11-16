-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianFirstPassageZeroDiscount
-- name    : Kyprianou.Ch01.brownianFirstPassageZeroDiscount
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T20:09:49.852192+00:00
-- url     : https://prove2.me/theorems/26c84fa4-9c04-437f-a087-602c77debba7
-- title:
--   Undrifted Brownian upper first passage has unit zero-discount Laplace mass
-- statement:
--   Exercise 1.7: The zero-discount value of the first upper passage Laplace payoff is the indicator of finite first passage. Undrifted nondegenerate Brownian motion almost surely hits every strictly positive level in finite time. Hence the payoff is integrable with expectation one. This is the exact boundary q=0 step missing from the previously published positive-discount identity; it can also be obtained as q decreases to zero by dominated convergence from the positive-q Brownian passage transform.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.7, recurrent standard Brownian motion and its index-one-half first-passage subordinator.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianFirstPassageZeroDiscount
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hmeas : ∀ t : ℝ≥0, Measurable (B t))
    (s : ℝ) (hs : 0 < s) :
    Integrable (Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstUpperPassage B s) 0) P ∧
    (∫ ω, Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstUpperPassage B s) 0 ω ∂P) = 1 := by sorry

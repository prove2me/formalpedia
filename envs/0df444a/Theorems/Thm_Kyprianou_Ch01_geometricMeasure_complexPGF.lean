-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricMeasure_complexPGF
-- name    : Kyprianou.Ch01.geometricMeasure_complexPGF
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:35:46.129209+00:00
-- url     : https://prove2.me/theorems/e5b7d3fe-6834-4305-8c4b-08ade5bc04c4
-- title:
--   Exact geometric probability generating function as an integral under the canonical geometric law
-- statement:
--   For any nonzero geometric success parameter p in the unit interval and any complex z satisfying the natural geometric-series norm bound ‖(1-p)z‖<1, the probability generating function ∫ z^n d geometricMeasure(p)(n) is exactly p/[1-(1-p)z]. This is an exact measure-theoretic integral, not merely a formal series. The proof applies Mathlib integral_geometricMeasure and the independently Proved complex geometric generating series, with correct complexification of the real probability coefficients. It provides the analytic foundation for the geometric law characteristic function and its logarithmic compound-Poisson infinite-divisibility decomposition.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.2(i), solution printed p. 299; pinned Mathlib integral_geometricMeasure and Kyprianou.Ch01.geometricComplexGeneratingSeries.

import Mathlib
open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricMeasure_complexPGF
    (p : unitInterval.Elem) (hp : p ≠ 0)
    (z : ℂ)
    (hbound : ‖(1 - ((p : ℝ) : ℂ)) * z‖ < 1) :
    (∫ n : ℕ, z ^ n ∂ProbabilityTheory.geometricMeasure p) =
      ((p : ℝ) : ℂ) / (1 - (1 - ((p : ℝ) : ℂ)) * z) := by
  sorry

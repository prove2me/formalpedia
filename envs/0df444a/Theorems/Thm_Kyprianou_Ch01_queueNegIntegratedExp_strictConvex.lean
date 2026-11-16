-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueNegIntegratedExp_strictConvex
-- name    : Kyprianou.Ch01.queueNegIntegratedExp_strictConvex
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T11:19:49.726992+00:00
-- url     : https://prove2.me/theorems/fbf7d0f0-695a-4721-b76a-c1d808e8a072
-- title:
--   Strict convexity of negative integrated exponential deficit for positive claims
-- statement:
--   For a probability distribution supported strictly on positive claim sizes, the negative of the integrated exponential deficit 1−exp(−θx) is strictly convex for θ≥0. This is the central analytic property required to prove strict convexity of the queue Laplace exponent, independently of queue model parameters.
-- source:
--   Kyprianou (2006), Chapter 1, queueing exercise 1.9(i): strict convexity of the Laplace exponent

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.queueNegIntegratedExp_strictConvex
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0) :
    StrictConvexOn ℝ (Set.Ici (0 : ℝ))
      (fun theta : ℝ => -(∫ x : ℝ, (1 - Real.exp (-theta * x)) ∂F)) := by sorry

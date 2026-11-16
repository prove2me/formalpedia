-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_strictConvex
-- name    : Kyprianou.Ch01.queueLaplaceExponent_strictConvex
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:29:26.276761+00:00
-- url     : https://prove2.me/theorems/ac89a33c-8bb7-4b98-a757-520226dece4f
-- title:
--   Strict convexity of the M/G/1 risk exponent
-- statement:
--   Strict convexity of the Laplace exponent of a unit-drift compound Poisson risk process on the nonnegative half-line under a positive arrival rate and positive claim-size law.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.9(i), original theorem b284c2f7-67e4-4cda-a713-7bf561654166.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueLaplaceExponent_strictConvex
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (queueLaplaceExponent rate F) := by sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_diverges
-- name    : Kyprianou.Ch01.queueLaplaceExponent_diverges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:29:26.561127+00:00
-- url     : https://prove2.me/theorems/2324201d-4c5d-4459-9227-b255059fb37a
-- title:
--   Positive-tail divergence of the M/G/1 Laplace exponent
-- statement:
--   As the Laplace parameter tends to positive infinity, the unit-drift queue/risk exponent tends to positive infinity, because its discounted jump transform is bounded.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.9(i), original theorem b284c2f7-67e4-4cda-a713-7bf561654166.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueLaplaceExponent_diverges
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    Tendsto (queueLaplaceExponent rate F) atTop atTop := by sorry

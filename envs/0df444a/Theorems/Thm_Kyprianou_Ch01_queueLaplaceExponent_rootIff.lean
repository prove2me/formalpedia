-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_rootIff
-- name    : Kyprianou.Ch01.queueLaplaceExponent_rootIff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:29:24.392215+00:00
-- url     : https://prove2.me/theorems/6fc4e182-14f6-4163-bc08-3afbf7f57dfd
-- title:
--   Cramér positive root iff queue load exceeds unity
-- statement:
--   There exists a strictly positive zero of the M/G/1 Laplace exponent exactly when the arrival rate multiplied by the positive mean service time exceeds one.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.9(i), original theorem b284c2f7-67e4-4cda-a713-7bf561654166.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueLaplaceExponent_rootIff
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    ((∃ theta : ℝ, 0 < theta ∧ queueLaplaceExponent rate F theta = 0) ↔ 1 < (rate : ℝ) * mu) := by sorry

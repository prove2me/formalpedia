-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_rootUnique
-- name    : Kyprianou.Ch01.queueLaplaceExponent_rootUnique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:29:29.197429+00:00
-- url     : https://prove2.me/theorems/18bcbae8-bf33-4f19-9f2e-912f004abcf7
-- title:
--   Uniqueness of a positive Cramér root
-- statement:
--   There is at most one positive zero of the queue/risk Laplace exponent in the positive rate, positive claim regime.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.9(i), original theorem b284c2f7-67e4-4cda-a713-7bf561654166.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueLaplaceExponent_rootUnique
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    (∀ theta theta' : ℝ,
    0 < theta → 0 < theta' →
    queueLaplaceExponent rate F theta = 0 →
    queueLaplaceExponent rate F theta' = 0 →
    theta = theta') := by sorry

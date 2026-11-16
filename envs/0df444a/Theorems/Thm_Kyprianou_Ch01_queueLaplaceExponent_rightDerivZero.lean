-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_rightDerivZero
-- name    : Kyprianou.Ch01.queueLaplaceExponent_rightDerivZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T12:06:54.404419+00:00
-- url     : https://prove2.me/theorems/49adcebc-70be-40ad-8031-6a7407947920
-- title:
--   Right derivative at zero of the M/G/1 queue exponent equals one minus traffic load
-- statement:
--   For positive claim sizes with finite mean, differentiating the exponential deficit under the probability integral gives right derivative of the queue exponent at zero as one minus rate times mean.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(i), Cramer positive root existence criterion

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueLaplaceExponent_rightDerivZero
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    HasDerivWithinAt (queueLaplaceExponent rate F)
      (1 - (rate : ℝ) * mu) (Set.Ici (0 : ℝ)) 0 := by sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_continuousOn
-- name    : Kyprianou.Ch01.queueLaplaceExponent_continuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T12:06:50.382059+00:00
-- url     : https://prove2.me/theorems/a8254ba5-fc6c-460c-a280-a23164b6f966
-- title:
--   Continuity on nonnegative arguments of the queue exponent
-- statement:
--   The Laplace queue exponent is continuous on the nonnegative axis for a positive-claim probability distribution of finite mean.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(i), Cramer positive root existence criterion

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.queueLaplaceExponent_continuousOn
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    ContinuousOn (queueLaplaceExponent rate F) (Set.Ici (0 : ℝ)) := by sorry

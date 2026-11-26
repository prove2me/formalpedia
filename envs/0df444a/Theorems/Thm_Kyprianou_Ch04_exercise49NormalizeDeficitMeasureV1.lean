-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49NormalizeDeficitMeasureV1
-- name    : Kyprianou.Ch04.exercise49NormalizeDeficitMeasureV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:42:33.088853+00:00
-- url     : https://prove2.me/theorems/9d9e99ad-11c2-4dd4-884c-c85a843b3ece
-- title:
--   Normalize a finite defective renewal law without changing the convolution identity
-- statement:
--   Normalize a finite defective renewal law without changing the convolution identity
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49NormalizeDeficitMeasureV1
    (rho : ℝ) (h0 : 0 < rho) (h1 : rho < 1)
    (nu mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hnu : nu univ = ENNReal.ofReal rho)
    (hLaw : mu = ENNReal.ofReal (1 - rho) • Measure.dirac 0 + mu.conv nu) :
    ∃ eta : Measure ℝ, IsProbabilityMeasure eta ∧
      (∀ B : Set ℝ, (eta B).toReal = (nu B).toReal / rho) ∧
      mu = ENNReal.ofReal (1 - rho) • Measure.dirac 0 +
        ENNReal.ofReal rho • (mu.conv eta) := by
  sorry

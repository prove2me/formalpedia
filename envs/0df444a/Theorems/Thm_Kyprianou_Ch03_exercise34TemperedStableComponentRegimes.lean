-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise34TemperedStableComponentRegimes
-- name    : Kyprianou.Ch03.exercise34TemperedStableComponentRegimes
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T10:07:49.525985+00:00
-- url     : https://prove2.me/theorems/79b5c96b-706a-4e74-9c56-7bf2ba767469
-- title:
--   Exercise 3.4(ii)-(iv): gamma and stable Esscher classifications
-- statement:
--   The alpha=0 jump measure has the gamma-process Laplace exponent up to drift; the alpha=1 one-sided Cauchy and other stable-index regimes are recovered exactly by reversing the Esscher tilt. The finite-activity alpha<0 part is included in Exercise 3.4's decomposition obligation.
-- source:
--   Kyprianou (2006), Exercise 3.4(ii)-(iv), printed p. 84; solutions p. 314.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise34TemperedStableComponentRegimes
(c gamma : ℝ) (hc : 0 < c) (hgamma : 0 < gamma) :
    (∀ q : ℝ, 0 ≤ q →
      (∫ x in Set.Ioi (0 : ℝ),
        (1 - Real.exp (-q * x)) ∂
          (temperedStablePositiveMeasure c 0 gamma)) =
        c * Real.log (1 + q / gamma)) ∧
    (temperedStablePositiveMeasure c 1 gamma).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
      temperedStablePositiveMeasure c 1 0 ∧
    (∀ alpha : ℝ, (0 < alpha ∧ alpha < 1) ∨
        (1 < alpha ∧ alpha < 2) →
      (temperedStablePositiveMeasure c alpha gamma).withDensity
        (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
        temperedStablePositiveMeasure c alpha 0) := by
  sorry

end Kyprianou.Ch03

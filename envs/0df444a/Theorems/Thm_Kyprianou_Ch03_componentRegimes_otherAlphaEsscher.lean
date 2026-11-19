-- Prove2me | Theorems.Thm_Kyprianou_Ch03_componentRegimes_otherAlphaEsscher
-- name    : Kyprianou.Ch03.componentRegimes_otherAlphaEsscher
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:22.301208+00:00
-- url     : https://prove2.me/theorems/b7892740-afb4-46e4-8adb-c9fcf7b68e77
-- title:
--   Exercise 3.4 supplementary regimes part 3: otherAlphaEsscher
-- statement:
--   The full original mathematical subpart 3 of Exercise 3.4 supplementary regimes, with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.4 supplementary regimes, part 3

import Mathlib
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem componentRegimes_otherAlphaEsscher
(c gamma : ℝ) (hc : 0 < c) (hgamma : 0 < gamma) :
    (∀ alpha : ℝ, (0 < alpha ∧ alpha < 1) ∨
        (1 < alpha ∧ alpha < 2) →
      (temperedStablePositiveMeasure c alpha gamma).withDensity
        (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
        temperedStablePositiveMeasure c alpha 0) := by
  sorry

end Kyprianou.Ch03

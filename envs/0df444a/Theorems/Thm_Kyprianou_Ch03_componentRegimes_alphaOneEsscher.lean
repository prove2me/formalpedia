-- Prove2me | Theorems.Thm_Kyprianou_Ch03_componentRegimes_alphaOneEsscher
-- name    : Kyprianou.Ch03.componentRegimes_alphaOneEsscher
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:22.607381+00:00
-- url     : https://prove2.me/theorems/256844cc-c410-4685-a099-367c66c9b011
-- title:
--   Exercise 3.4 supplementary regimes part 2: alphaOneEsscher
-- statement:
--   The full original mathematical subpart 2 of Exercise 3.4 supplementary regimes, with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.4 supplementary regimes, part 2

import Mathlib
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem componentRegimes_alphaOneEsscher
(c gamma : ℝ) (hc : 0 < c) (hgamma : 0 < gamma) :
    (temperedStablePositiveMeasure c 1 gamma).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
      temperedStablePositiveMeasure c 1 0 := by
  sorry

end Kyprianou.Ch03

-- Prove2me | Theorems.Thm_Kyprianou_Ch03_componentRegimes_gammaLaplace
-- name    : Kyprianou.Ch03.componentRegimes_gammaLaplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:11.629781+00:00
-- url     : https://prove2.me/theorems/1052c053-a5d3-4c3a-b7df-7dbb1339f55c
-- title:
--   Exercise 3.4 supplementary regimes part 1: gammaLaplace
-- statement:
--   The full original mathematical subpart 1 of Exercise 3.4 supplementary regimes, with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.4 supplementary regimes, part 1

import Mathlib
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem componentRegimes_gammaLaplace
(c gamma : ℝ) (hc : 0 < c) (hgamma : 0 < gamma) :
    (∀ q : ℝ, 0 ≤ q →
      (∫ x in Set.Ioi (0 : ℝ),
        (1 - Real.exp (-q * x)) ∂
          (temperedStablePositiveMeasure c 0 gamma)) =
        c * Real.log (1 + q / gamma)) := by
  sorry

end Kyprianou.Ch03

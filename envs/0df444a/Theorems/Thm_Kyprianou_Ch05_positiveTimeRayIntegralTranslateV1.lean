-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveTimeRayIntegralTranslateV1
-- name    : Kyprianou.Ch05.positiveTimeRayIntegralTranslateV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T22:02:36.138286+00:00
-- url     : https://prove2.me/theorems/1d8afb63-1da5-5ed0-a384-cd8a6a1ba3c3
-- title:
--   Translate a nonnegative integral on an open real ray
-- statement:
--   Use Avram's cumulative-measure translation lemma with Lebesgue measures restricted to the two open rays. The cumulative masses are the common interval length.
-- source:
--   Kyprianou (2006), Chapter 5, Exercise 5.8.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology Kyprianou.Ch05
open scoped Classical Topology

theorem Kyprianou.Ch05.positiveTimeRayIntegralTranslateV1
    (a : ℝ) (g : ℝ → ENNReal) (hg : Measurable g) :
    (∫⁻ t in Ioi a, g t ∂volume) = ∫⁻ s in Ioi (0 : ℝ), g (a+s) ∂volume := by
  sorry

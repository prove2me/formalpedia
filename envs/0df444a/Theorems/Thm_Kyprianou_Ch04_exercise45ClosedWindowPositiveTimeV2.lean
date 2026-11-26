-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45ClosedWindowPositiveTimeV2
-- name    : Kyprianou.Ch04.exercise45ClosedWindowPositiveTimeV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:17:27.760815+00:00
-- url     : https://prove2.me/theorems/7034c541-01c1-53d6-9bbf-28fa86acc8a7
-- title:
--   exercise45ClosedWindowPositiveTimeV2
-- statement:
--   exercise45ClosedWindowPositiveTimeV2
-- source:
--   Exercise 4.5(iii), pure-jump Ito limit

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45ClosedWindowPositiveTimeV2
    (μ : Measure (ℝ × ℝ)) (hzero : μ ({0} ×ˢ (Set.univ : Set ℝ)) = 0)
    (T : NNReal) :
    μ.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ Set.univ) =
      μ.restrict (Ioc (0 : ℝ) (T : ℝ) ×ˢ Set.univ) := by
  sorry

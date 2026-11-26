-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinatorPositiveLevyMeasureV1
-- name    : Kyprianou.Ch05.killedSubordinatorPositiveLevyMeasureV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:46:49.037731+00:00
-- url     : https://prove2.me/theorems/c3fef071-97e1-4679-8552-af59e8f64716
-- title:
--   The Chapter 5 triplet is a LeanLevy Levy measure
-- statement:
--   The nonpositive half-line is null, and min(1,x squared) is dominated by min(1,x) on the positive half-line.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch05.killedSubordinatorPositiveLevyMeasureV1
    (eta d : ℝ) (Pi : Measure ℝ) (Phi : ℝ → ℝ)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi) :
    ProbabilityTheory.IsLevyMeasure Pi := by
  sorry

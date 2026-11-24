-- Prove2me | Theorems.Thm_Kyprianou_Ch03_delayedOpenInfValueInClosedNeighbourhoodV1
-- name    : Kyprianou.Ch03.delayedOpenInfValueInClosedNeighbourhoodV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:13:53.987727+00:00
-- url     : https://prove2.me/theorems/3176560c-4d00-49e4-bc6c-04a61e02d772
-- title:
--   Finite delayed open infimum has value in the closed neighbourhood
-- statement:
--   The hitting set is nonempty at a finite infimum. Approach its infimum from the right using witnesses; the right-continuous value belongs to the closed thickening.
-- source:
--   Kyprianou (2006), Theorem 3.3, delayed closed hitting approximation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.delayedOpenInfValueInClosedNeighbourhoodV1
    (f : NNReal → ℝ)
    (hrc : ∀ t : NNReal, ContinuousWithinAt f (Set.Ici t) t)
    (B : Set ℝ) (r : ℝ) (a u : NNReal)
    (hu : (u : WithTop NNReal) = sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ f t ∈ Metric.thickening r B})) :
    f u ∈ Metric.cthickening r B := by
  sorry

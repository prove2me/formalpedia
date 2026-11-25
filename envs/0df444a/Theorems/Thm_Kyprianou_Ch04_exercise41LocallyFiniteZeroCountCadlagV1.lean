-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41LocallyFiniteZeroCountCadlagV1
-- name    : Kyprianou.Ch04.exercise41LocallyFiniteZeroCountCadlagV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:01:55.146539+00:00
-- url     : https://prove2.me/theorems/2a7a57f3-af0c-40f5-a703-0061933a2772
-- title:
--   Locally finite set of zero visits has càdlàg cumulative cardinality
-- statement:
--   If the set of positive-time visits to zero is finite on every compact interval then its cumulative cardinality is right-continuous with a left limit at every positive time. The theorem is deterministic and applies directly to the actual pathwise visit set.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.1(i), printed pages 105–106.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41LocallyFiniteCountRestrictionV1
import Theorems.Thm_Kyprianou_Ch04_exercise41FiniteVisitCountCardinalityCadlagV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41LocallyFiniteZeroCountCadlagV1
    (Z : Set NNReal) (hFinite : ∀ T : NNReal, (Z ∩ Iic T).Finite) :
    (∀ t : NNReal, ContinuousWithinAt
      (fun u : NNReal => ((Z ∩ Iic u).ncard : ℝ)) (Ici t) t) ∧
    (∀ t : NNReal, 0 < t → ∃ l : ℝ, Tendsto
      (fun u : NNReal => ((Z ∩ Iic u).ncard : ℝ))
      (nhdsWithin t (Iio t)) (nhds l)) := by
  sorry

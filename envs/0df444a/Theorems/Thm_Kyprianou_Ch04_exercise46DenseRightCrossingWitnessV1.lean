-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46DenseRightCrossingWitnessV1
-- name    : Kyprianou.Ch04.exercise46DenseRightCrossingWitnessV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T23:36:36.872395+00:00
-- url     : https://prove2.me/theorems/c0904dd6-cbfd-55ce-89bb-af28ef101a62
-- title:
--   A strict right-continuous crossing is observed in any dense time set
-- statement:
--   Use right continuity to preserve a strict crossing on a right neighbourhood, then choose a dense observation inside that neighbourhood before the deadline.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46DenseRightCrossingWitnessV1
    (D : Set NNReal) (hD : Dense D) (f : NNReal → Real)
    (s t : NNReal) (hst : s < t)
    (hR : ContinuousWithinAt f (Ici s) s)
    (H : Real) (hH : H < f s) :
    ∃ r ∈ D, s < r ∧ r < t ∧ H < f r := by
  sorry

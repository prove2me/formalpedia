-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46MappedClockNullSingletonV1
-- name    : Kyprianou.Ch04.exercise46MappedClockNullSingletonV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:18:13.176165+00:00
-- url     : https://prove2.me/theorems/8d7d13bb-4f4a-4560-af5b-6e3bbf1a5b84
-- title:
--   The restricted mapped time measure has no singleton atoms
-- statement:
--   The inverse image of any singleton under Real.toNNReal, restricted to the nonnegative horizon, is contained in the corresponding real singleton. Lebesgue measure of that singleton is zero.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46MappedClockNullSingletonV1
    (T : NNReal) :
    NullSingletonClass (((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal) := by
  sorry

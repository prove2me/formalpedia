-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46CDFWithoutZeroAtomV1
-- name    : Kyprianou.Ch04.exercise46CDFWithoutZeroAtomV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T10:11:34.743917+00:00
-- url     : https://prove2.me/theorems/dc9003a3-34c1-53cb-a973-8e09029b9d58
-- title:
--   Partition the CDF event into the positive part and the zero atom, using finite-measure additivity and the vanishing real mass of the atom.
-- statement:
--   Partition the CDF event into the positive part and the zero atom, using finite-measure additivity and the vanishing real mass of the atom.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.6(ii).

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46CDFWithoutZeroAtomV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (I : Omega → ENNReal) (hm : Measurable I)
    (hz : (P {omega | I omega = 0}).toReal = 0)
    (a : ENNReal) :
    (P {omega | I omega ≤ a}).toReal =
      (P {omega | 0 < I omega ∧ I omega ≤ a}).toReal := by
  sorry

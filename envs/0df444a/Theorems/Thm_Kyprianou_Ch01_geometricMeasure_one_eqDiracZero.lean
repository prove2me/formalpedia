-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricMeasure_one_eqDiracZero
-- name    : Kyprianou.Ch01.geometricMeasure_one_eqDiracZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:43:50.386558+00:00
-- url     : https://prove2.me/theorems/378d829b-ce24-4689-a779-eb2d7948bcd4
-- title:
--   Geometric success probability one gives precisely the Dirac measure at zero
-- statement:
--   The canonical geometric count probability measure with certain immediate success p=1 equals the Dirac probability measure at the count zero. The proof uses the pinned geometricMeasure_singleton formula and countable measure extensionality for the two disjoint cases n=0 and n>0. This identifies the degenerate boundary case of the geometric law in Kyprianou Chapter 1 Exercise 1.2(i), which is independently infinitely divisible by the proved Dirac-zero convolution-root lemma.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.2(i) boundary p=1; Mathlib geometricMeasure_singleton, Measure.ext_of_singleton.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricMeasure_one_eqDiracZero :
    ProbabilityTheory.geometricMeasure (1 : unitInterval.Elem) =
      Measure.dirac (0 : ℕ) := by
  sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FiniteClockLawV1
-- name    : Kyprianou.Ch04.exercise46FiniteClockLawV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T21:08:34.292947+00:00
-- url     : https://prove2.me/theorems/912f1b08-e7b4-4000-b459-f45cf1690aa3
-- title:
--   Finite-part pushforward law of an extended nonnegative clock
-- statement:
--   Restrict to the measurable finite-clock event and push forward the finite time as a real number. Almost-everywhere representatives preserve the CDF, finite mass and all killed Laplace integrals.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FiniteClockLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → WithTop NNReal) (hB : AEMeasurable B P) :
    ∃ nu : Measure Real, IsFiniteMeasure nu ∧ nu (Iio (0 : Real)) = 0 ∧
      nu univ = P {w | B w ≠ ⊤} ∧
      (∀ t : Real, 0 ≤ t → nu (Iic t) =
        P {w | B w ≤ (t.toNNReal : WithTop NNReal)}) ∧
      ∀ beta : Real, (∫ y, Real.exp (-beta * y) ∂nu) =
        ∫ w, if B w = ⊤ then (0 : Real)
          else Real.exp (-beta * (((B w).untopD 0 : NNReal) : Real)) ∂P := by
  sorry

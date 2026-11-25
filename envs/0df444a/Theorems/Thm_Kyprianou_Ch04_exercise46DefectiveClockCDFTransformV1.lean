-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46DefectiveClockCDFTransformV1
-- name    : Kyprianou.Ch04.exercise46DefectiveClockCDFTransformV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T21:02:14.208863+00:00
-- url     : https://prove2.me/theorems/a2c36a94-a952-5cd7-b8e0-05cbceb4ff5a
-- title:
--   Defective extended clock CDF Laplace transform
-- statement:
--   For an almost-everywhere measurable extended nonnegative time, Tonelli gives the Laplace transform of its defective CDF for positive rates; at zero the transform equals the probability of finite time. Infinity contributes zero.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46DefectiveClockCDFTransformV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → WithTop NNReal) (hB : AEMeasurable B P)
    (beta : Real) (hb : 0 ≤ beta) :
    (if beta = 0 then (P {omega | B omega ≠ ⊤}).toReal
      else beta * (∫ t in Ici (0 : Real), Real.exp (-beta * t) *
        (P {omega | B omega ≤ (Real.toNNReal t : WithTop NNReal)}).toReal ∂volume)) =
      ∫ omega, if B omega = ⊤ then (0 : Real)
        else Real.exp (-beta * (((B omega).untopD 0 : NNReal) : Real)) ∂P := by
  sorry

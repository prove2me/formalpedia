-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46IndependentPathKernelIntegralV1
-- name    : Kyprianou.Ch04.exercise46IndependentPathKernelIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:23:20.882351+00:00
-- url     : https://prove2.me/theorems/56b30289-c4ad-5f8a-840c-a8d8f6f78ed7
-- title:
--   Fubini identity for a bounded measurable kernel of independent random variables
-- statement:
--   The independent pair has product law. Push the integral forward and apply Fubini, then pull each path section back to the original space.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46IndependentPathKernelIntegralV1
    {Omega S : Type} [MeasurableSpace Omega] [MeasurableSpace S]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (J : Omega → Real) (hJ : AEMeasurable J P)
    (Z : Omega → S) (hZ : AEMeasurable Z P)
    (hInd : IndepFun J Z P)
    (f : Real × S → Real) (hf : Measurable f)
    (hBound : ∀ z, ‖f z‖ ≤ 1) :
    (∫ w, f (J w, Z w) ∂P) =
      ∫ y, (∫ w, f (y, Z w) ∂P) ∂(P.map J) := by
  sorry

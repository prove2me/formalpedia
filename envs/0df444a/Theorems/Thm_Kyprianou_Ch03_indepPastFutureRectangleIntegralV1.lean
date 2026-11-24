-- Prove2me | Theorems.Thm_Kyprianou_Ch03_indepPastFutureRectangleIntegralV1
-- name    : Kyprianou.Ch03.indepPastFutureRectangleIntegralV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:27:37.729066+00:00
-- url     : https://prove2.me/theorems/e6829f49-8cc6-44ea-9ac3-5c9f5d06cc39
-- title:
--   Conditional past indicator integrals agree on past-future rectangles
-- statement:
--   Integrating the conditional expectation of an intermediate-sigma-algebra indicator over a past-future rectangle yields the original indicator integral. Independence factors out the future event, and the past event is handled by the defining conditional expectation property.
-- source:
--   Kyprianou (2006), Chapter 3, past-future independence; conditional expectation rectangle argument.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.indepPastFutureRectangleIntegralV1
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m g h : MeasurableSpace Omega)
    (hmg : m ≤ g) (hgh : g ≤ m ⊔ h) (hjoin : m ⊔ h ≤ mΩ)
    (hInd : @Indep Omega g h mΩ P)
    (A : Set Omega) (hA : MeasurableSet[g] A)
    (C D : Set Omega) (hC : MeasurableSet[m] C) (hD : MeasurableSet[h] D) :
    (∫ x in C ∩ D, (P[A.indicator (fun _ => (1 : ℝ)) | m]) x ∂P) =
      ∫ x in C ∩ D, A.indicator (fun _ => (1 : ℝ)) x ∂P := by sorry

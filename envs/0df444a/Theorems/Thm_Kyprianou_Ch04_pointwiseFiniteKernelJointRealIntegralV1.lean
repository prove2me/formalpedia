-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pointwiseFiniteKernelJointRealIntegralV1
-- name    : Kyprianou.Ch04.pointwiseFiniteKernelJointRealIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:20:46.522594+00:00
-- url     : https://prove2.me/theorems/145ba6cd-c09b-43f0-87a1-63f5d760c6a6
-- title:
--   Bounded real integrals against pointwise finite random measures
-- statement:
--   A bounded jointly measurable real integrand has measurable integrals against pointwise finite random measures.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem pointwiseFiniteKernelJointRealIntegralV1 {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (R : Ω → Measure E) (hR : ∀ S : Set E, MeasurableSet S → Measurable (fun w => R w S))
    (hFin : ∀ w, IsFiniteMeasure (R w))
    (g : Ω × E → ℝ) (hg : Measurable g)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C) :
    Measurable (fun w => ∫ z, g (w,z) ∂(R w)) := by
  sorry
end Kyprianou.Ch04

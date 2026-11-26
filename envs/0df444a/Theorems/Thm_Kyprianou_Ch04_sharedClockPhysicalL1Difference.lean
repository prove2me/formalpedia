-- Prove2me | Theorems.Thm_Kyprianou_Ch04_sharedClockPhysicalL1Difference
-- name    : Kyprianou.Ch04.sharedClockPhysicalL1Difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:53:10.453306+00:00
-- url     : https://prove2.me/theorems/759e6df8-12a5-5c40-a5bf-acaf4c42d6a2
-- title:
--   Physical L1 continuity under shared expected clock measure
-- statement:
--   For two integrable predictable representatives on a common expected clock measure, the physical compensated integrals have an expected absolute difference bounded by twice their L1 distance.
-- source:
--   Kyprianou (2006), Exercise 4.4, physical integral approximation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_Kyprianou_Ch04_aeFiniteExpectedAbsoluteRandomIntegral
import Theorems.Thm_Kyprianou_Ch04_physicalCompensatedL1DifferenceBound
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- Shared expected-clock measure controls physical compensated L1 differences. -/
theorem Kyprianou.Ch04.sharedClockPhysicalL1Difference
    {Omega E A : Type} [MeasurableSpace Omega] [MeasurableSpace E] [MeasurableSpace A]
    (P : Measure Omega) (mu : Measure A)
    (R : Omega → Measure E) (S : Measure E) (q : Omega → E → A)
    (hq : ∀ w, Measurable (q w))
    (hR : ∀ k : A → ENNReal, Measurable k →
      AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂(R w)) P ∧
      (∫⁻ w, ∫⁻ z, k (q w z) ∂(R w) ∂P) = ∫⁻ a, k a ∂mu)
    (hS : ∀ k : A → ENNReal, Measurable k →
      AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂S) P ∧
      (∫⁻ w, ∫⁻ z, k (q w z) ∂S ∂P) = ∫⁻ a, k a ∂mu)
    (f g : A → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f mu) (hgi : Integrable g mu) :
    let I := fun k : A → ℝ => fun w =>
      (∫ z, k (q w z) ∂(R w)) - ∫ z, k (q w z) ∂S
    Integrable (I f) P ∧ Integrable (I g) P ∧
      (∫ w, |I f w - I g w| ∂P) ≤ 2 * ∫ a, |f a - g a| ∂mu := by
  sorry

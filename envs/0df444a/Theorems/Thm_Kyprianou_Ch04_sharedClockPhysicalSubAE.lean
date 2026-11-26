-- Prove2me | Theorems.Thm_Kyprianou_Ch04_sharedClockPhysicalSubAE
-- name    : Kyprianou.Ch04.sharedClockPhysicalSubAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:21:27.32682+00:00
-- url     : https://prove2.me/theorems/80397247-2655-5164-9457-79957e017904
-- title:
--   sharedClockPhysicalSubAE
-- statement:
--   The physical compensated integral respects subtraction almost surely on measurable integrable kernels.
-- source:
--   Kyprianou (2006), Exercise 4.4, physical completion.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- The physical compensated integral is additive under subtraction on integrable kernels. -/
theorem Kyprianou.Ch04.sharedClockPhysicalSubAE
    {Omega E A : Type} [MeasurableSpace Omega] [MeasurableSpace E] [MeasurableSpace A]
    (P : Measure Omega) (mu : Measure A) (R : Omega → Measure E) (S : Measure E)
    (q : Omega → E → A) (hq : ∀ w, Measurable (q w))
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
    I (f - g) =ᵐ[P] I f - I g := by
  sorry

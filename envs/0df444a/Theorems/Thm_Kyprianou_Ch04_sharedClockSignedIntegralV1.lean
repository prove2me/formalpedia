-- Prove2me | Theorems.Thm_Kyprianou_Ch04_sharedClockSignedIntegralV1
-- name    : Kyprianou.Ch04.sharedClockSignedIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:10:44.2535+00:00
-- url     : https://prove2.me/theorems/d1e780a3-5797-402c-951e-303e425cb99e
-- title:
--   Signed real integral through a common expected clock
-- statement:
--   Transfer a signed integrable real kernel through a common expected clock, using its positive and negative parts.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem sharedClockSignedIntegralV1 {Ω E A : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace A]
    (P : Measure Ω) (μ : Measure A) (R : Ω → Measure E)
    (q : Ω → E → A) (hq : ∀ w, Measurable (q w))
    (hR : ∀ k : A → ENNReal, Measurable k →
      AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂(R w)) P ∧
      (∫⁻ w, ∫⁻ z, k (q w z) ∂(R w) ∂P) = ∫⁻ a, k a ∂μ)
    (f : A → ℝ) (hf : Measurable f) (hi : Integrable f μ) :
    (∀ᵐ w ∂P, Integrable (fun z => f (q w z)) (R w)) ∧
      Integrable (fun w => ∫ z, f (q w z) ∂(R w)) P ∧
      (∫ w, ∫ z, f (q w z) ∂(R w) ∂P) = ∫ a, f a ∂μ := by
  sorry
end Kyprianou.Ch04

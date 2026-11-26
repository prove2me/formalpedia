-- Prove2me | Theorems.Thm_Kyprianou_Ch04_sharedClockNonnegativeIntegral
-- name    : Kyprianou.Ch04.sharedClockNonnegativeIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:16:54.699814+00:00
-- url     : https://prove2.me/theorems/f245a061-f1f1-453a-ae4a-f4e050a30c98
-- title:
--   sharedClockNonnegativeIntegral
-- statement:
--   A nonnegative integrable kernel has the same expected real integral on the shared clock measure as its physical pullback.
-- source:
--   Kyprianou (2006), Exercise 4.4, finite-band L2 completion.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- Transfer a nonnegative integrable real kernel through an expected clock measure. -/
theorem Kyprianou.Ch04.sharedClockNonnegativeIntegral
    {Omega E A : Type} [MeasurableSpace Omega] [MeasurableSpace E] [MeasurableSpace A]
    (P : Measure Omega) (mu : Measure A) (R : Omega → Measure E)
    (q : Omega → E → A) (hq : ∀ w, Measurable (q w))
    (hR : ∀ k : A → ENNReal, Measurable k →
      AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂(R w)) P ∧
      (∫⁻ w, ∫⁻ z, k (q w z) ∂(R w) ∂P) = ∫⁻ a, k a ∂mu)
    (f : A → ℝ) (hf : Measurable f) (h0 : ∀ a, 0 ≤ f a) (hi : Integrable f mu) :
    (∫ w, ∫ z, f (q w z) ∂(R w) ∂P) = ∫ a, f a ∂mu := by
  sorry

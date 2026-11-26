-- Prove2me | Theorems.Thm_Kyprianou_Ch04_sharedClockSignedIntegrabilityV1
-- name    : Kyprianou.Ch04.sharedClockSignedIntegrabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:12:51.302787+00:00
-- url     : https://prove2.me/theorems/b0bf1214-b0c6-4413-b111-8b16be6088d7
-- title:
--   Pathwise and outer integrability for a shared expected clock
-- statement:
--   Finite expected absolute mass in a shared clock gives pathwise almost-sure and outer signed integrability.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem sharedClockSignedIntegrabilityV1 {Ω E A : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace A]
    (P : Measure Ω) (μ : Measure A) (R : Ω → Measure E)
    (q : Ω → E → A) (hq : ∀ w, Measurable (q w))
    (hR : ∀ k : A → ENNReal, Measurable k →
      AEMeasurable (fun w => ∫⁻ z, k (q w z) ∂(R w)) P ∧
      (∫⁻ w, ∫⁻ z, k (q w z) ∂(R w) ∂P) = ∫⁻ a, k a ∂μ)
    (f : A → ℝ) (hf : Measurable f) (hi : Integrable f μ) :
    (∀ᵐ w ∂P, Integrable (fun z => f (q w z)) (R w)) ∧
      Integrable (fun w => ∫ z, f (q w z) ∂(R w)) P := by
  sorry
end Kyprianou.Ch04

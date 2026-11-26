-- Prove2me | Theorems.Thm_Kyprianou_Ch04_aeFiniteExpectedAbsoluteRandomIntegral
-- name    : Kyprianou.Ch04.aeFiniteExpectedAbsoluteRandomIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:49:43.587973+00:00
-- url     : https://prove2.me/theorems/ed3a96d0-a355-4c1d-9abe-eb4d41c96968
-- title:
--   Finite expected absolute random integral
-- statement:
--   Finite expected absolute mass and almost-everywhere measurable extended clocks give pathwise integrability and integrable signed and absolute clocks.
-- source:
--   Kyprianou (2006), Exercise 4.4, supporting physical L1 approximation lemma.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- Finite expected absolute mass yields a.e pathwise and outer integrability. -/
theorem Kyprianou.Ch04.aeFiniteExpectedAbsoluteRandomIntegral
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (R : Omega → Measure E)
    (f : Omega → E → ℝ)
    (hm : ∀ᵐ w ∂P, AEStronglyMeasurable (f w) (R w))
    (hL : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal |f w z| ∂(R w)) P)
    (hLp : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal (f w z) ∂(R w)) P)
    (hLn : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal (-f w z) ∂(R w)) P)
    (hfin : (∫⁻ w, ∫⁻ z, ENNReal.ofReal |f w z| ∂(R w) ∂P) < ⊤) :
    (∀ᵐ w ∂P, Integrable (f w) (R w)) ∧
    Integrable (fun w => ∫ z, |f w z| ∂(R w)) P ∧
    (∫ w, ∫ z, |f w z| ∂(R w) ∂P) =
      (∫⁻ w, ∫⁻ z, ENNReal.ofReal |f w z| ∂(R w) ∂P).toReal ∧
    Integrable (fun w => ∫ z, f w z ∂(R w)) P := by
  sorry

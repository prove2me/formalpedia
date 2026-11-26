-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteRandomIntegralSplitAE
-- name    : Kyprianou.Ch04.finiteRandomIntegralSplitAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:15:50.87643+00:00
-- url     : https://prove2.me/theorems/daf367a9-07b8-58f9-9793-a9c555cad2d0
-- title:
--   finiteRandomIntegralSplitAE
-- statement:
--   Finite expected positive and negative masses justify pathwise signed integrability and splitting.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- Finite signed-part masses justify pathwise integrability and subtraction. -/
theorem Kyprianou.Ch04.finiteRandomIntegralSplitAE {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (R : Omega → Measure E) (f : Omega → E → ℝ)
    (hf : ∀ w, Measurable (f w))
    (hP : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal (max (f w z) 0) ∂(R w)) P)
    (hN : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal (max (-f w z) 0) ∂(R w)) P)
    (hp : (∫⁻ w, ∫⁻ z, ENNReal.ofReal (max (f w z) 0) ∂(R w) ∂P) < ⊤)
    (hn : (∫⁻ w, ∫⁻ z, ENNReal.ofReal (max (-f w z) 0) ∂(R w) ∂P) < ⊤) :
    ∀ᵐ w ∂P, Integrable (f w) (R w) ∧
      (∫ z, f w z ∂(R w)) =
        (∫ z, max (f w z) 0 ∂(R w)) - ∫ z, max (-f w z) 0 ∂(R w) := by
  sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch04_subcriticalGeometricWorkloadLawTransform
-- name    : Kyprianou.Ch04.subcriticalGeometricWorkloadLawTransform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:32:57.849108+00:00
-- url     : https://prove2.me/theorems/7deffa7d-aa0a-4b92-b359-888ecb182c21
-- title:
--   The geometric workload probability law has nonnegative support and the subcritical Laplace ratio.
-- statement:
--   The geometric workload probability law has nonnegative support and the subcritical Laplace ratio.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.subcriticalGeometricWorkloadLawTransform
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    let eta := ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun x : ℝ => L.ν (Iio (-x))/(ENNReal.ofReal L.drift*rho))
    let convPow : ℕ → Measure ℝ := Nat.rec (Measure.dirac (0 : ℝ)) (fun _ m => m.conv eta)
    0 < rho → rho < 1 →
    ∀ mu : Measure ℝ, IsProbabilityMeasure mu →
      (∀ B : Set ℝ, MeasurableSet B → mu B = ∑' n : ℕ, ((1-rho)*rho^n) * (convPow n B)) →
      mu (Iio 0) = 0 ∧ ∀ a : ℝ, 0 < a → (∫ x, Real.exp (-a*x) ∂mu) = (L.drift-M.toReal)*a/L.ψ a := by
  sorry

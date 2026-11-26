-- Prove2me | Theorems.Thm_Kyprianou_Ch04_subcriticalZeroInitialWorkloadLimitLaw
-- name    : Kyprianou.Ch04.subcriticalZeroInitialWorkloadLimitLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:32:55.264667+00:00
-- url     : https://prove2.me/theorems/2b4a8b99-126f-458c-86d8-76f7b6bb2b84
-- title:
--   The zero-initial workload converges weakly to a nonnegative law with the subcritical Laplace ratio.
-- statement:
--   The zero-initial workload converges weakly to a nonnegative law with the subcritical Laplace ratio.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.subcriticalZeroInitialWorkloadLimitLaw
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
    ∃ mu : Measure ℝ, IsProbabilityMeasure mu ∧ mu (Iio 0) = 0 ∧
      (∀ a : ℝ, 0 < a → (∫ x, Real.exp (-a*x) ∂mu) = (L.drift-M.toReal)*a/L.ψ a) ∧
      (∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun t : NNReal => ∫ z, f (sSup ((fun s : NNReal => L.X s z) '' Iic t) - L.X t z) ∂P)
          atTop (nhds (∫ x, f x ∂mu))) := by
  sorry

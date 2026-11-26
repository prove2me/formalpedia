-- Prove2me | Theorems.Thm_Kyprianou_Ch04_subcriticalWeakLimitLaplaceTransform
-- name    : Kyprianou.Ch04.subcriticalWeakLimitLaplaceTransform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:39:13.004465+00:00
-- url     : https://prove2.me/theorems/53b3e0f6-f2d7-5a0a-919d-1de3477a1f7d
-- title:
--   Every such nonnegative weak limit has the subcritical Laplace transform.
-- statement:
--   Every such nonnegative weak limit has the subcritical Laplace transform.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.subcriticalWeakLimitLaplaceTransform
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
    ∀ nu : Measure ℝ, nu (Iio 0) = 0 →
      (∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun t : NNReal => ∫ z, f (sSup ((fun s : NNReal => L.X s z) '' Iic t) - L.X t z) ∂P)
          atTop (nhds (∫ x, f x ∂nu))) →
      ∀ a : ℝ, 0 < a → (∫ x, Real.exp (-a*x) ∂nu) = (L.drift-M.toReal)*a/L.ψ a := by
  sorry

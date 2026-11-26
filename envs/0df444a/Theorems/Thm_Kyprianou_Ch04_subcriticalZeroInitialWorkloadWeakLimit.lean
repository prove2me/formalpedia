-- Prove2me | Theorems.Thm_Kyprianou_Ch04_subcriticalZeroInitialWorkloadWeakLimit
-- name    : Kyprianou.Ch04.subcriticalZeroInitialWorkloadWeakLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:39:07.765274+00:00
-- url     : https://prove2.me/theorems/ff5003ff-5264-4e70-9edf-4212946ad767
-- title:
--   The zero-initial workload has a weak limit supported on the nonnegative halfline.
-- statement:
--   The zero-initial workload has a weak limit supported on the nonnegative halfline.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.subcriticalZeroInitialWorkloadWeakLimit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
    ∃ mu : Measure ℝ, IsProbabilityMeasure mu ∧ mu (Iio 0) = 0 ∧
      (∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun t : NNReal => ∫ z, f (sSup ((fun s : NNReal => L.X s z) '' Iic t) - L.X t z) ∂P)
          atTop (nhds (∫ x, f x ∂mu))) := by
  sorry

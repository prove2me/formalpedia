-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryWorkloadGeometricMeasureAtom
-- name    : Kyprianou.Ch04.stationaryWorkloadGeometricMeasureAtom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:03:18.740816+00:00
-- url     : https://prove2.me/theorems/44eca21a-bbfc-4b20-a9a5-50f1108a475f
-- title:
--   Exact zero atom of the stationary geometric convolution measure
-- statement:
--   The exact geometric-convolution measure in Theorem 4.10 has mass 1 minus traffic intensity at zero, since the integrated-tail kernel is absolutely continuous and all positive convolution powers are atomless.
-- source:
--   Kyprianou (2006) Theorem 4.10 p. 100, geometric convolution stationary law, exact source interface.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.stationaryWorkloadGeometricMeasureAtom
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    let eta : Measure Real :=
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun x : Real =>
          L.ν (Set.Iio (-x)) /
            (ENNReal.ofReal L.drift * rho))
    let convPow : Nat → Measure Real :=
      Nat.rec (Measure.dirac (0 : Real))
        (fun _ mu => mu.conv eta)
    0 < rho → rho < 1 →
      ∀ mu : Measure Real,
        (∀ B : Set Real, MeasurableSet B →
          mu B =
            ∑' n : Nat,
              ((1 - rho) * rho ^ n) * (convPow n B)) →
        mu {0} = 1 - rho := by
  sorry

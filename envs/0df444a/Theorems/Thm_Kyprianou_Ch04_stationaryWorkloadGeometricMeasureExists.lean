-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryWorkloadGeometricMeasureExists
-- name    : Kyprianou.Ch04.stationaryWorkloadGeometricMeasureExists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T20:20:28.308143+00:00
-- url     : https://prove2.me/theorems/6d58ce5b-9a9c-44fd-ba09-77f3e5d7480d
-- title:
--   Stationary geometric convolution candidate measure for bounded-variation Lévy workload
-- statement:
--   For spectrally negative bounded variation input with positive drift and subcritical traffic, construct a probability measure from the exact integrated Lévy-tail law and its convolution powers; its Borel values are exactly the Pollaczek–Khintchine geometric series appearing in Theorem 4.10. This does not yet assert the zero atom or weak workload limit.
-- source:
--   Kyprianou (2006) Theorem 4.10 p. 100, geometric convolution stationary law, exact source interface.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.stationaryWorkloadGeometricMeasureExists
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
      ∃ mu : Measure Real,
        IsProbabilityMeasure mu ∧
        IsProbabilityMeasure eta ∧
        ∀ B : Set Real, MeasurableSet B →
          mu B =
            ∑' n : Nat,
              ((1 - rho) * rho ^ n) * (convPow n B) := by
  sorry

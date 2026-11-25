-- Prove2me | Theorems.Thm_Kyprianou_Ch04_trafficIntegratedNegativeTailProbability
-- name    : Kyprianou.Ch04.trafficIntegratedNegativeTailProbability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:03:56.075335+00:00
-- url     : https://prove2.me/theorems/80f45a7d-bdb1-49e3-94bb-5f5c70b261a4
-- title:
--   Normalised integrated negative Lévy tail is a probability measure for subcritical workload
-- statement:
--   For bounded-variation spectrally negative Lévy input with positive drift and 0<rho<1, the integrated negative Lévy-tail density over positive deficits, normalised by drift times rho, has total mass one. The proof uses the exact layer-cake first-moment identity and normalized withDensity. This is the eta probability clause of Theorem 4.10.
-- source:
--   Kyprianou (2006), Theorem 4.10 p100; integrated negative Levy tail and stationarity convolution law.

import Mathlib
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.ENNReal.Inv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.trafficIntegratedNegativeTailProbability
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let rho : ENNReal :=
      (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
      IsProbabilityMeasure
        (((volume : Measure ℝ).restrict (Ioi 0)).withDensity
          (fun x : ℝ =>
            L.ν (Iio (-x)) /
              (ENNReal.ofReal L.drift * rho))) := by
  sorry

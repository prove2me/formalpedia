-- Prove2me | Theorems.Thm_Kyprianou_Ch04_integratedNegativeTailLaplaceTransform
-- name    : Kyprianou.Ch04.integratedNegativeTailLaplaceTransform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:32:54.716458+00:00
-- url     : https://prove2.me/theorems/b14d5d3a-b43b-5656-bf73-7207d36a3fb5
-- title:
--   Integrated negative tail law has the normalized BV deficit transform.
-- statement:
--   Integrated negative tail law has the normalized BV deficit transform.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.integratedNegativeTailLaplaceTransform {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (r : ENNReal) (a : ℝ) (ha : 0 < a) :
    let eta := ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun x : ℝ => L.ν (Iio (-x)) / (ENNReal.ofReal L.drift * r))
    (∫⁻ x, ENNReal.ofReal (Real.exp (-a*x)) ∂eta) =
      (ENNReal.ofReal L.drift * r)⁻¹ *
        ENNReal.ofReal ((L.drift*a-L.ψ a)/a) := by
  sorry

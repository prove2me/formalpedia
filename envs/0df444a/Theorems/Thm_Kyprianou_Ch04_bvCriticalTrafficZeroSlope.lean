-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvCriticalTrafficZeroSlope
-- name    : Kyprianou.Ch04.bvCriticalTrafficZeroSlope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:15:48.275123+00:00
-- url     : https://prove2.me/theorems/6d688533-5c26-4bb0-8cd6-3f012e4e687b
-- title:
--   Critical and greater traffic forces zero nonnegative secant infimum
-- statement:
--   If all secants were bounded below by a positive epsilon, the normalized jump deficit would be bounded by drift minus a smaller positive epsilon. The moment characterisation contradicts traffic at least one.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvCriticalTrafficZeroSlope
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (htraffic : 1 ≤ (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) / ENNReal.ofReal L.drift) :
    max 0 (sInf ((fun a : ℝ => L.ψ a / a) '' Ioi 0)) = 0 := by
  sorry

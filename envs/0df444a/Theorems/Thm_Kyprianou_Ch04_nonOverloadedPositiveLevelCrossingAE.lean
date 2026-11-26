-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nonOverloadedPositiveLevelCrossingAE
-- name    : Kyprianou.Ch04.nonOverloadedPositiveLevelCrossingAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:34:29.318076+00:00
-- url     : https://prove2.me/theorems/21a89e15-4498-5b44-b752-4f512002a237
-- title:
--   Under traffic at most one and positive drift, every fixed positive level is crossed almost surely by the original process.
-- statement:
--   Under traffic at most one and positive drift, every fixed positive level is crossed almost surely by the original process.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.nonOverloadedPositiveLevelCrossingAE {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (hr : (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) / ENNReal.ofReal L.drift ≤ 1)
    (x : ℝ) (hx : 0 < x) :
    ∀ᵐ z ∂P, ∃ t : NNReal, x < L.X t z := by
  sorry

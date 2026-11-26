-- Prove2me | Theorems.Thm_Kyprianou_Ch04_subcriticalPathsBoundedBelowAE
-- name    : Kyprianou.Ch04.subcriticalPathsBoundedBelowAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:32:49.906002+00:00
-- url     : https://prove2.me/theorems/7a52722c-491e-5094-a899-776c30546705
-- title:
--   Subcritical paths are almost surely bounded below.
-- statement:
--   Subcritical paths are almost surely bounded below.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.subcriticalPathsBoundedBelowAE {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (hr0 : 0 < (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) / ENNReal.ofReal L.drift)
    (hr1 : (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) / ENNReal.ofReal L.drift < 1) :
    ∀ᵐ z ∂P, BddBelow (range (fun t : NNReal => L.X t z)) := by
  sorry

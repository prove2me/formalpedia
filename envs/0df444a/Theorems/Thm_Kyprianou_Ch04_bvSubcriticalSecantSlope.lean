-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvSubcriticalSecantSlope
-- name    : Kyprianou.Ch04.bvSubcriticalSecantSlope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:21:20.834705+00:00
-- url     : https://prove2.me/theorems/cd5ab600-0d1a-570f-8204-5ee401f7f68b
-- title:
--   Subcritical BV traffic secant infimum
-- statement:
--   The normalized deficit moment characterization gives drift less jump mean as a lower bound on all secants. Applying the characterization to the secant infimum gives the reverse inequality.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvSubcriticalSecantSlope
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
    max 0 (sInf ((fun a : ℝ => L.ψ a / a) '' Ioi 0)) = L.drift - M.toReal ∧
      0 < L.drift - M.toReal := by
  sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvSubcriticalSecantLower
-- name    : Kyprianou.Ch04.bvSubcriticalSecantLower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:29:14.384293+00:00
-- url     : https://prove2.me/theorems/75705d82-22b1-4d21-bfe9-131aa453d0d5
-- title:
--   A finite negative jump mean bounds the secant below by drift minus jump mean.
-- statement:
--   A finite negative jump mean bounds the secant below by drift minus jump mean.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvSubcriticalSecantLower
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (hMtop : (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) ≠ ⊤)
    (a : ℝ) (ha : 0 < a) :
    L.drift - (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν).toReal ≤ L.ψ a / a := by
  sorry

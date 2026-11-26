-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvSecantLowerBoundsJumpMean
-- name    : Kyprianou.Ch04.bvSecantLowerBoundsJumpMean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:29:17.833812+00:00
-- url     : https://prove2.me/theorems/f5ff9e2c-f570-4632-8e24-f07b25998fdb
-- title:
--   A uniform lower secant bound implies an upper bound on the negative jump mean.
-- statement:
--   A uniform lower secant bound implies an upper bound on the negative jump mean.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvSecantLowerBoundsJumpMean
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (m : ℝ) (hm : ∀ a : ℝ, 0 < a → m ≤ L.ψ a / a) :
    (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν) ≤ ENNReal.ofReal (L.drift-m) := by
  sorry

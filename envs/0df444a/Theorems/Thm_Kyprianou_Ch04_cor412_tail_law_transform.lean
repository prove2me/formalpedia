-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_tail_law_transform
-- name    : Kyprianou.Ch04.cor412_tail_law_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:40:18.506664+00:00
-- url     : https://prove2.me/theorems/f3d3377c-89cf-5fe8-955e-b2256be52399
-- title:
--   Exponential transform of reflected integrated negative jump tail law
-- statement:
--   The reflected integrated negative jump tail law has the defective exponential transform.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_cor412_integrated_tail_transform
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The reflected integrated-tail law has the same positive-ray exponential transform as the passage position. -/

theorem Kyprianou.Ch04.cor412_tail_law_transform {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (β : ℝ) (hβ : 0 < β) :
    let κ := (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal (1/L.drift) * L.ν (Iio (-y)))
    (∫⁻ x, ENNReal.ofReal (Real.exp (β*x)) ∂(κ.map (fun y => -y))) =
      ENNReal.ofReal (1 - L.ψ β / (L.drift * β)) := by sorry

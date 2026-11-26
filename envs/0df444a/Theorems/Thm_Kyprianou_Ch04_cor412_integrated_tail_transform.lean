-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_integrated_tail_transform
-- name    : Kyprianou.Ch04.cor412_integrated_tail_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:48:38.451799+00:00
-- url     : https://prove2.me/theorems/97619d11-d62e-4d02-a7bf-fd18cd42e9be
-- title:
--   Laplace transform of the reflected integrated negative Levy tail
-- statement:
--   Laplace transform of the reflected integrated negative Levy tail.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_discounted_positive_jump_tail_transform
import Theorems.Thm_Kyprianou_Ch04_bvNormalizedExponentGapV1
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.cor412_integrated_tail_transform
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (β : ℝ) (hβ : 0 < β) :
    (∫⁻ y in Ioi (0 : ℝ), L.ν (Iio (-y)) *
      ENNReal.ofReal (Real.exp (-β * y))) =
      ENNReal.ofReal ((L.drift * β - L.ψ β) / β) := by sorry

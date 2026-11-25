-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvNormalizedExponentGapV1
-- name    : Kyprianou.Ch04.bvNormalizedExponentGapV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:06:40.854673+00:00
-- url     : https://prove2.me/theorems/763611f4-13b0-48c8-9365-76db7a5e9858
-- title:
--   Normalized BV exponent deficit as an extended jump integral
-- statement:
--   Apply the proved positive-magnitude BV exponent formula and convert the normalized nonnegative jump deficit to its lintegral. Outside the negative half-line its positive part vanishes, so the unrestricted lintegral agrees with the restricted one.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1, analytic traffic classification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.bvNormalizedExponentGapV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)

    (a : Real) (ha : 0 < a) :
    (∫⁻ y : Real, ENNReal.ofReal ((1 - Real.exp (a*y))/a) ∂L.ν) =
      ENNReal.ofReal ((L.drift*a - L.ψ a)/a) := by
  sorry

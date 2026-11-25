-- Prove2me | Theorems.Thm_Kyprianou_Ch04_expMeasureComplexTransform
-- name    : Kyprianou.Ch04.expMeasureComplexTransform
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T07:56:47.840843+00:00
-- url     : https://prove2.me/theorems/b66a5349-d6a4-40f0-b6f0-f9c4a0de570e
-- title:
--   Complex exponential transform of arbitrary positive-rate exponential measure
-- statement:
--   Evaluate the exponential density over the positive half-line using Mathlib's complex improper integral; generalise the proved rate-one transform.
-- source:
--   Kyprianou (2006), Exercise 4.8(ii), Wiener–Hopf transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.expMeasureComplexTransform
    (q : ℝ) (hq : 0 < q) (z : ℂ) (hz : z.re < q) :
    (∫ t : ℝ, Complex.exp (z * t) ∂expMeasure q) = (q : ℂ) / ((q : ℂ) - z) := by
  sorry

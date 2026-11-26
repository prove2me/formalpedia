-- Prove2me | Theorems.Thm_Kyprianou_Ch04_negativeTailLaplaceLayercake
-- name    : Kyprianou.Ch04.negativeTailLaplaceLayercake
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:23:55.149809+00:00
-- url     : https://prove2.me/theorems/de8eee75-a76e-4760-8491-cc1cc5108233
-- title:
--   Discounted negative Lévy tail layercake
-- statement:
--   The discounted negative Lévy tail integral equals the integrated normalised jump deficit.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.negativeTailLaplaceLayercake (nu : Measure ℝ) (hnu : nu (Ici 0) = 0) (a : ℝ) (ha : 0 < a) :
    (∫⁻ t in Ioi (0 : ℝ), nu (Iio (-t)) * ENNReal.ofReal (Real.exp (-a*t))) =
      ∫⁻ y : ℝ, ENNReal.ofReal ((1 - Real.exp (a*y))/a) ∂nu := by
  sorry

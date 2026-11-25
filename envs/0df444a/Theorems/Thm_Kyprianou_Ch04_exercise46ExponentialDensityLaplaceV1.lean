-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46ExponentialDensityLaplaceV1
-- name    : Kyprianou.Ch04.exercise46ExponentialDensityLaplaceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:57:39.362026+00:00
-- url     : https://prove2.me/theorems/141c9bd6-e274-4119-bed4-4f71bd0a2095
-- title:
--   Laplace transform of a positive exponential density
-- statement:
--   Combine the exponentials and integrate the nonnegative decaying exponential.
-- source:
--   Kyprianou (2006), Exercise 4.6(iii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46ExponentialDensityLaplaceV1
    (a b s : Real) (ha : 0 ≤ a) (hb : 0 < b) (hs : 0 ≤ s) :
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s * x))
      ∂(((volume : Measure Real).restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (a * Real.exp (-b*x))))) =
      ENNReal.ofReal (a / (b+s)) := by
  sorry

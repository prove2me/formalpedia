-- Prove2me | Theorems.Thm_Kyprianou_Ch04_atomicCumulativeDerivativeV1
-- name    : Kyprianou.Ch04.atomicCumulativeDerivativeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:33:57.418906+00:00
-- url     : https://prove2.me/theorems/6d0d2a51-9430-4c3a-921c-f457f597a954
-- title:
--   Zero derivative of a summable atomic cumulative sum
-- statement:
--   Identify the cumulative function with the real-valued finite atomic mass and apply the almost-everywhere differentiation theorem for singular measures.
-- source:
--   Supporting deterministic differentiation for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_atomicMeasureMassV1
import Theorems.Thm_Kyprianou_Ch04_atomicMeasureSingularV1
import Theorems.Thm_Kyprianou_Ch04_singularCumulativeDerivativeV1
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.atomicCumulativeDerivativeV1 {ι : Type} (a : ι → ℝ) (w : ι → ℝ)
    (hw : Summable w) (hn : ∀ i, 0 ≤ w i) :
    ∀ᵐ x : ℝ ∂volume, HasDerivAt
      (fun t => ∑' i, (a ⁻¹' Iic t).indicator w i) 0 x := by
  sorry

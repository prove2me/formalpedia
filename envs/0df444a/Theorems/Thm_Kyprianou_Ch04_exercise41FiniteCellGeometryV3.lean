-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FiniteCellGeometryV3
-- name    : Kyprianou.Ch04.exercise41FiniteCellGeometryV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:06:25.331415+00:00
-- url     : https://prove2.me/theorems/1e886b16-f098-4ebf-8902-506a7c6db44b
-- title:
--   At most two successful cells for a finite grid and slope cylinder
-- statement:
--   At most two successful cells for a finite grid and slope cylinder
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise41FiniteCellGeometryV3
    (x : NNReal → ℝ) (I : Finset ℕ)
    (D : ℕ → Finset NNReal) (b : ℕ → NNReal) (R : Finset NNReal)
    (a h d : ℝ) (hh : 0 < h) (hd : 0 < d)
    (hcell : ∀ i ∈ I, ∀ t ∈ D i,
      a + (i : ℝ) * h ≤ (t : ℝ) ∧
      (t : ℝ) < a + ((i : ℝ) + 1) * h)
    (hR : ∀ i ∈ I, ∀ j ∈ I, i < j →
      ∀ s ∈ D i, ∀ t ∈ D j, t - s ∈ R) :
    let C : NNReal → Set Unit := fun t => {w | |x t| < d * h / 8}
    let τ : ℕ → NNReal := fun i => exercise41GridFirstV2 (D i) C (b i) ()
    let S := I.filter fun i =>
      (∃ t ∈ D i, () ∈ C t) ∧
        ∀ u ∈ R, d / 2 * (u : ℝ) ≤ x (τ i + u) - x (τ i)
    S.card ≤ 2  := by
  sorry

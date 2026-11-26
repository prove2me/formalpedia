-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45UniformWeightedErrorV4
-- name    : Kyprianou.Ch04.exercise45UniformWeightedErrorV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:37:32.754369+00:00
-- url     : https://prove2.me/theorems/47cfec99-f83f-4012-af5a-995f9bf5a55c
-- title:
--   exercise45UniformWeightedErrorV4
-- statement:
--   exercise45UniformWeightedErrorV4
-- source:
--   Exercise 4.5: uniform finite cutoff grids

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45UniformWeightedErrorV4
    {ι : Type} (S : Finset ι) (T : NNReal)
    (D : ℕ → NNReal → ℝ) (d : NNReal → ℝ)
    (J : ι → ℕ → NNReal → ℝ) (j : ι → NNReal → ℝ)
    (b : ℝ) (a : ι → ℝ)
    (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |D n t - d t| < δ)
    (hJ : ∀ r ∈ S, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T,
      |J r n t - j r t| < δ) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T,
      |(b * D n t + ∑ r ∈ S, a r * J r n t) -
        (b * d t + ∑ r ∈ S, a r * j r t)| < δ := by
  sorry

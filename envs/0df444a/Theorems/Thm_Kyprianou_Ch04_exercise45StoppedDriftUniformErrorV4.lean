-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45StoppedDriftUniformErrorV4
-- name    : Kyprianou.Ch04.exercise45StoppedDriftUniformErrorV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:32:47.960827+00:00
-- url     : https://prove2.me/theorems/7c9dd143-90fe-4c51-9578-02ee79a178ee
-- title:
--   exercise45StoppedDriftUniformErrorV4
-- statement:
--   exercise45StoppedDriftUniformErrorV4
-- source:
--   Exercise 4.5: stopped finite cutoff grids

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45StoppedDriftUniformErrorV4
    (T : NNReal) (H : NNReal → ℝ) (C : ℝ)
    (hb : ∀ r, |H r| ≤ C)
    (hl : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r))) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal, t ≤ T →
      |(∑ i ∈ Finset.range (n+1),
        H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) *
          ((min t (T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal)) : NNReal).toReal -
           (min t (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) : NNReal).toReal)) -
        (∫ s in Icc (0 : ℝ) (t : ℝ), H s.toNNReal)| < δ := by
  sorry

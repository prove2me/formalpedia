-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45MaskedFirstCellV5
-- name    : Kyprianou.Ch04.exercise45MaskedFirstCellV5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T20:38:23.73421+00:00
-- url     : https://prove2.me/theorems/13d3d0f8-9f01-4869-a465-238997d7fad7
-- title:
--   The short first cell vanishes uniformly by right continuity
-- statement:
--   The short first cell vanishes uniformly by right continuity
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii), uniform probability transfer

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45MaskedFirstCellV5 (Y : NNReal → ℝ) (T : NNReal) (K : ℝ)
    (hY : ContinuousWithinAt Y (Ici 0) 0) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal,
      |K * (|Y (min t (T / (n : NNReal))) - Y 0|)| < δ := by
  sorry

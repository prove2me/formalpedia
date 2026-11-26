-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45StrictDyadicCrossingV5
-- name    : Kyprianou.Ch04.exercise45StrictDyadicCrossingV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:20:02.069752+00:00
-- url     : https://prove2.me/theorems/c898b129-db9c-41f2-b7af-9c0b8dfa6430
-- title:
--   Strict compact right-continuous crossing and dyadic clock bounds
-- statement:
--   Strict compact right-continuous crossing and dyadic clock bounds
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii), uniform probability transfer

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45StrictDyadicCrossingV5 (f : NNReal → ℝ) (T : NNReal)
    (hr : ∀ t, ContinuousWithinAt f (Ici t) t) (δ : ℝ) :
    let q (j : ℕ) (k : Fin (2^j+1)) : NNReal :=
      (k.val : NNReal) / (2 : NNReal)^j * T
    (∀ j k, q j k ≤ T) ∧
      ((∃ t ≤ T, δ < |f t|) ↔ ∃ j k, δ < |f (q j k)|) := by
  sorry

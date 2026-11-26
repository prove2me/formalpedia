-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45MaskedGridDifferenceV5
-- name    : Kyprianou.Ch04.exercise45MaskedGridDifferenceV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:37:39.165288+00:00
-- url     : https://prove2.me/theorems/4d61003c-0278-4c27-9660-82cd3b1fd810
-- title:
--   The masked grid differs only by the bounded first cell
-- statement:
--   The masked grid differs only by the bounded first cell
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii), uniform probability transfer

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45MaskedGridDifferenceV5 (Y H : NNReal → ℝ) (T t : NNReal) (n : ℕ)
    (K : ℝ) (hK : 0 ≤ K) (hb : |H 0| ≤ K) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    let G : ℝ := ∑ k ∈ Finset.range n, H (u k) * (Y (v (k+1)) - Y (v k))
    let A : ℝ := ∑ k ∈ Finset.range n, (if u k = 0 then 0 else H (u k)) *
      (Y (v (k+1)) - Y (v k))
    |G-A| ≤ K * |Y (min t (T / (n : NNReal))) - Y 0| := by
  sorry

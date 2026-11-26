-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45StoppedAffineGridDecompV4
-- name    : Kyprianou.Ch04.exercise45StoppedAffineGridDecompV4
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:37:32.609318+00:00
-- url     : https://prove2.me/theorems/5b35f020-6feb-4645-997d-091b9826ef1f
-- title:
--   exercise45StoppedAffineGridDecompV4
-- statement:
--   exercise45StoppedAffineGridDecompV4
-- source:
--   Exercise 4.5: uniform finite cutoff grids

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45StoppedAffineGridDecompV4
    (T t : NNReal) (ht : t ≤ T) (n : ℕ) (S : Finset NNReal)
    (a H Y : NNReal → ℝ) (b : ℝ)
    (hY : ∀ t ≤ T, Y t = b * (t : ℝ) + ∑ r ∈ S, if r ≤ t then a r else 0) :
    let u : ℕ → NNReal := fun i => T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
    (∑ i ∈ Finset.range (n+1), H (u i) * (Y (min t (u (i+1))) - Y (min t (u i)))) =
      b * (∑ i ∈ Finset.range (n+1), H (u i) *
        ((min t (u (i+1)) : NNReal).toReal - (min t (u i) : NNReal).toReal)) +
      ∑ r ∈ S, a r * (∑ i ∈ Finset.range (n+1),
        if min t (u i) < r ∧ r ≤ min t (u (i+1)) then H (u i) else 0) := by
  sorry

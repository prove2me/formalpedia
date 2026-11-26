-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45StoppedSingleAtomErrorV4
-- name    : Kyprianou.Ch04.exercise45StoppedSingleAtomErrorV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:31:14.152603+00:00
-- url     : https://prove2.me/theorems/e2956729-e4bd-5cc5-a573-2fe09515b410
-- title:
--   exercise45StoppedSingleAtomErrorV4
-- statement:
--   exercise45StoppedSingleAtomErrorV4
-- source:
--   Exercise 4.5: stopped finite cutoff grids

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45StoppedSingleAtomErrorV4
    (T r : NNReal) (hr : 0 < r) (hrT : r ≤ T) (H : NNReal → ℝ)
    (hH : Tendsto H (𝓝[<] r) (𝓝 (H r))) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal,
      |(∑ i ∈ Finset.range (n+1),
        if min t (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) < r ∧
          r ≤ min t (T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal))
        then H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) else 0) -
        (if r ≤ t then H r else 0)| < δ := by
  sorry

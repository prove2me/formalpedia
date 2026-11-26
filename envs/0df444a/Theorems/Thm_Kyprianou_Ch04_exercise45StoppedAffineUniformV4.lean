-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45StoppedAffineUniformV4
-- name    : Kyprianou.Ch04.exercise45StoppedAffineUniformV4
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:37:30.568004+00:00
-- url     : https://prove2.me/theorems/c97b7bd1-979d-5aaa-affa-c1ecbc75121d
-- title:
--   exercise45StoppedAffineUniformV4
-- statement:
--   exercise45StoppedAffineUniformV4
-- source:
--   Exercise 4.5: uniform finite cutoff grids

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45StoppedAffineUniformV4
    (T : NNReal) (S : Finset NNReal) (a H Y : NNReal → ℝ) (b C : ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T)
    (hY : ∀ t ≤ T, Y t = b * (t : ℝ) + ∑ r ∈ S, if r ≤ t then a r else 0)
    (hH : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r)))
    (hb : ∀ r, |H r| ≤ C) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T,
      |(∑ i ∈ Finset.range (n+1),
        let u := T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
        let v := T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal)
        H u * (Y (min t v) - Y (min t u))) -
        (b * (∫ s in Icc (0 : ℝ) (t : ℝ), H s.toNNReal) +
          ∑ r ∈ S, if r ≤ t then a r * H r else 0)| < δ := by
  sorry

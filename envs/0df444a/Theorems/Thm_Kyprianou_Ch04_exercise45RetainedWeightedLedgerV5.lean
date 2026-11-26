-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45RetainedWeightedLedgerV5
-- name    : Kyprianou.Ch04.exercise45RetainedWeightedLedgerV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:52:58.220528+00:00
-- url     : https://prove2.me/theorems/8562c1b1-97a0-4d92-b392-228dc66eea91
-- title:
--   Fixed-cutoff retained weighted atom and compensation ledger
-- statement:
--   Fixed-cutoff retained weighted atom and compensation ledger
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45RetainedWeightedLedgerV5 (R : Measure (ℝ × ℝ)) (ν : Measure ℝ) (T : NNReal) (e b : ℝ)
    (he : e < 1) (S : Finset NNReal) (j : NNReal → ℝ)
    (hs : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ e < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (H : ℝ → ℝ) (t : NNReal) (ht : t ≤ T) :
    let c := ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ ν
    b * (∫ s in Icc (0 : ℝ) (t : ℝ), H s) +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 * H z.1 ∂ R) +
      ((∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
        z.2 * H z.1 ∂ R) - ∫ s in Icc (0 : ℝ) (t : ℝ),
          ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x * H s ∂ ν) =
    (b-c) * (∫ s in Icc (0 : ℝ) (t : ℝ), H s) +
      ∑ r ∈ S, if r ≤ t then j r * H (r : ℝ) else 0 := by
  sorry

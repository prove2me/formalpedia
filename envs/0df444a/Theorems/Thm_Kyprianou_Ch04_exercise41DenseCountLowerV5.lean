-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41DenseCountLowerV5
-- name    : Kyprianou.Ch04.exercise41DenseCountLowerV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:42:47.891691+00:00
-- url     : https://prove2.me/theorems/46ed575b-ffa8-5ac2-86bc-35ec0e1761f2
-- title:
--   Every finite separated set of actual zeros is dominated by the dense-grid occupancy count
-- statement:
--   Every finite separated set of actual zeros is dominated by the dense-grid occupancy count
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41DenseCountLowerV5
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (S : Finset NNReal) (a h e : ℝ) (n : ℕ)
    (he : 0 < e) (j : NNReal → ℕ)
    (hc : ∀ s ∈ S, j s ∈ Finset.range n ∧
      a + (j s : ℝ) * h ≤ (s : ℝ) ∧
      (s : ℝ) < a + ((j s : ℝ) + 1) * h)
    (hinj : Set.InjOn j (S : Set NNReal))
    (hr : ∀ s ∈ S, ContinuousWithinAt x (Ici s) s)
    (hz : ∀ s ∈ S, x s = 0) :
    let A : ℕ → ℕ → Set Unit := fun m i =>
      {w | ∃ k < m, a + (i : ℝ) * h ≤ (q k : ℝ) ∧
        (q k : ℝ) < a + ((i : ℝ) + 1) * h ∧ |x (q k)| < e}
    (S.card : ℝ≥0∞) ≤ ⨆ m : ℕ, ∑ i ∈ Finset.range n,
      (A m i).indicator (fun _ : Unit => (1 : ℝ≥0∞)) ()  := by
  sorry

-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_cell_reindex
-- name    : Kyprianou.Ch04.ito43_cutoff_finite_cell_reindex
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:44:17.061281+00:00
-- url     : https://prove2.me/theorems/9dbdcfe7-d600-51aa-9536-f530f58cb8f0
-- title:
--   Retained stopped grid cells are indexed by finitely many actual jumps
-- statement:
--   Use finiteness of jumps above the cutoff, unique separated right-closed uniform cells and the proved no-spurious-large-cell compactness theorem applied to clipped cells. Reindex the grid sum on these distinct cells, and the absolutely finite jump series by the same finite set.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_finite_cell_reindex (X L : NNReal → ℝ)
    (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (K : NNReal → ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ s x z, |z| ≤ ρ → K s x z = 0)
    (T : NNReal) :
    let u : ℕ → ℕ → NNReal := fun n k => T * (k : NNReal) / (n : NNReal)
    let C : ℕ → NNReal → ℕ → ℝ := fun n t k =>
      K (u n k) (X (u n k))
        (X (min t (u n (k+1))) - X (min t (u n k)))
    let A : NNReal → NNReal → ℝ := fun t s =>
      if s ≤ t then K s (L s) (X s-L s) else 0
    ∃ (S : Finset NNReal) (j : NNReal → ℕ → ℕ),
      (∀ s ∈ S, 0 < s ∧ s ≤ T) ∧
      (∀ᶠ n : ℕ in atTop, ∀ s ∈ S,
        j s n < n ∧ u n (j s n) < s ∧ s ≤ u n (j s n+1)) ∧
      (∀ᶠ n : ℕ in atTop, ∀ t ≤ T,
        (∑ k ∈ Finset.range n, C n t k) = ∑ s ∈ S, C n t (j s n)) ∧
      (∀ t ≤ T, (∑' s : Ioc (0 : NNReal) t, K s.1 (L s.1) (X s.1-L s.1)) =
        ∑ s ∈ S, A t s) := by sorry

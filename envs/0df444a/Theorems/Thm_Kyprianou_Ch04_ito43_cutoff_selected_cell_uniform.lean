-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_selected_cell_uniform
-- name    : Kyprianou.Ch04.ito43_cutoff_selected_cell_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:44:14.695607+00:00
-- url     : https://prove2.me/theorems/459a6377-ae66-4e82-aa10-7ec1f488b36d
-- title:
--   Uniform cutoff kernel convergence within a selected jump cell
-- statement:
--   For a fixed positive jump time and shrinking right-closed cells, the lower endpoint tends strictly from the left. For stopped times at or after the jump the clipped right endpoint tends uniformly from the right. For times before the jump both endpoints are on the left or the increment is zero, hence eventually the cutoff is zero.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_selected_cell_uniform (X L : NNReal → ℝ)
    (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (K : NNReal → ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ s x z, |z| ≤ ρ → K s x z = 0)
    (T : NNReal)
    (s : NNReal) (hs : 0 < s) (hsT : s ≤ T) (j : ℕ → ℕ)
    (hj : ∀ᶠ n : ℕ in atTop,
      j n < n ∧ T * (j n : NNReal) / (n : NNReal) < s ∧
      s ≤ T * ((j n+1 : ℕ) : NNReal) / (n : NNReal)) :
    let u : ℕ → ℕ → NNReal := fun n k => T * (k : NNReal) / (n : NNReal)
    let C : ℕ → NNReal → ℕ → ℝ := fun n t k =>
      K (u n k) (X (u n k))
        (X (min t (u n (k+1))) - X (min t (u n k)))
    let A : NNReal → NNReal → ℝ := fun t s =>
      if s ≤ t then K s (L s) (X s-L s) else 0
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t ≤ T, |C n t (j n) - A t s| < ε := by sorry

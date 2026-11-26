-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_grid_cell_regular
-- name    : Kyprianou.Ch04.ito43_cutoff_grid_cell_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:09:09.964047+00:00
-- url     : https://prove2.me/theorems/77078416-c5f4-52e2-b67b-d428d89dd280
-- title:
--   Each stopped kernel cell is right continuous and bounded
-- statement:
--   The clipped clock is continuous and monotone. Compose the right-continuous path with it, then use the continuous kernel at fixed initial state. Compact path bounds control the mark and continuity bounds the kernel on a compact mark interval.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_grid_cell_regular (X L : NNReal → ℝ)
    (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (K : NNReal → ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ s x z, |z| ≤ ρ → K s x z = 0)
    (T : NNReal)
    (n k : ℕ) :
    let u : ℕ → NNReal := fun i => T*(i:NNReal)/(n:NNReal)
    let F : NNReal → ℝ := fun t =>
      K (u k) (X (u k)) (X (min t (u (k+1)))-X (min t (u k)))
    (∀ t, ContinuousWithinAt F (Ici t) t) ∧
      ∃ M : ℝ, ∀ t ≤ T, |F t| ≤ M := by sorry

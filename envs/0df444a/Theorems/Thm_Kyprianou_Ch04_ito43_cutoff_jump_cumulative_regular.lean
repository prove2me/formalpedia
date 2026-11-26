-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_jump_cumulative_regular
-- name    : Kyprianou.Ch04.ito43_cutoff_jump_cumulative_regular
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T20:09:07.502696+00:00
-- url     : https://prove2.me/theorems/7f2737ef-67a8-5ee0-8525-a3c062914402
-- title:
--   Cumulative cutoff jump sum is right continuous and bounded
-- statement:
--   Use the finite support and jump-series reindexing results on each larger horizon. The cumulative finite sum of weighted step indicators is right continuous and bounded.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_jump_cumulative_regular (X L : NNReal → ℝ)
    (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (K : NNReal → ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ s x z, |z| ≤ ρ → K s x z = 0)
    (T : NNReal) :
    let J : NNReal → ℝ := fun t =>
      ∑' s : Ioc (0:NNReal) t, K s.1 (L s.1) (X s.1-L s.1)
    (∀ t, ContinuousWithinAt J (Ici t) t) ∧
      ∃ M : ℝ, ∀ t ≤ T, |J t| ≤ M := by sorry

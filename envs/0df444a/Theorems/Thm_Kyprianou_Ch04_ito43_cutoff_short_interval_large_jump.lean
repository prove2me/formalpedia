-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_short_interval_large_jump
-- name    : Kyprianou.Ch04.ito43_cutoff_short_interval_large_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:06:18.271442+00:00
-- url     : https://prove2.me/theorems/aba537b2-6133-5305-8bf3-bd923d57594b
-- title:
--   Large increments on sufficiently short intervals contain a large jump
-- statement:
--   Choose a violating interval at each cofinal mesh resolution, use the proved generic Avram shrinking-interval theorem, and identify the canonical left limit with the supplied version at positive times.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_short_interval_large_jump (X L : NNReal → ℝ) (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (T : NNReal) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a b : NNReal,
      a ≤ b → b ≤ T → (b:ℝ)-(a:ℝ) ≤ (T:ℝ)/(n:ℝ) →
      ρ ≤ |X b-X a| →
      ∃ s : NNReal, a < s ∧ s ≤ b ∧ ρ ≤ |X s-L s| := by sorry

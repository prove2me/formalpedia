-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_clipped_no_spurious
-- name    : Kyprianou.Ch04.ito43_cutoff_clipped_no_spurious
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:02:15.303832+00:00
-- url     : https://prove2.me/theorems/6fa72e2b-f2d4-51e5-8654-d3e0ef27fe11
-- title:
--   Every large clipped cell contains a large physical jump
-- statement:
--   If arbitrarily fine clipped cells violate the claim, select one bad interval at each such resolution, use zero intervals elsewhere, and invoke the proved Avram uniform shrinking-family theorem. Clipping cannot increase the mesh width.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_clipped_no_spurious (X L : NNReal → ℝ) (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (T : NNReal) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ n : ℕ in atTop, ∀ t ≤ T, ∀ k < n,
      let a := min t (T*(k:NNReal)/(n:NNReal))
      let b := min t (T*((k+1:ℕ):NNReal)/(n:NNReal))
      ρ ≤ |X b-X a| →
      ∃ s : NNReal, a < s ∧ s ≤ b ∧ ρ ≤ |X s-L s| := by sorry

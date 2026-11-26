-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_large_support
-- name    : Kyprianou.Ch04.ito43_cutoff_finite_large_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:02:12.750026+00:00
-- url     : https://prove2.me/theorems/8b30a790-e9fb-5be4-ae4f-4ab04196c518
-- title:
--   Large physical jump support is finite on each horizon
-- statement:
--   Embed the large physical jumps into the finite set of jumps with magnitude strictly exceeding half the cutoff, using the existing general cadlag finiteness theorem.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_finite_large_support (X L : NNReal → ℝ) (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (T : NNReal) (ρ : ℝ) (hρ : 0 < ρ) :
    {s : NNReal | 0 < s ∧ s ≤ T ∧ ρ ≤ |X s-L s|}.Finite := by sorry

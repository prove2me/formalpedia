-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_series_reindex
-- name    : Kyprianou.Ch04.ito43_cutoff_finite_series_reindex
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:02:13.9892+00:00
-- url     : https://prove2.me/theorems/237b3c19-0982-4b01-b4ab-3e750d4f39d3
-- title:
--   Finite support reindexes the stopped jump series
-- statement:
--   Extend the sum on positive times by zero and use the finite support condition to reduce the infinite sum to the selected finite set.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_finite_series_reindex (G : NNReal → ℝ) (T : NNReal) (S : Finset NNReal)
    (hS : ∀ s ∈ S, 0 < s ∧ s ≤ T)
    (hz : ∀ s, 0 < s → s ≤ T → s ∉ S → G s = 0) :
    ∀ t ≤ T, (∑' s : Ioc (0 : NNReal) t, G s) =
      ∑ s ∈ S, if s ≤ t then G s else 0 := by sorry

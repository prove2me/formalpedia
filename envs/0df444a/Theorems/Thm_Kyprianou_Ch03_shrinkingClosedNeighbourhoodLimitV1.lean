-- Prove2me | Theorems.Thm_Kyprianou_Ch03_shrinkingClosedNeighbourhoodLimitV1
-- name    : Kyprianou.Ch03.shrinkingClosedNeighbourhoodLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:27:50.639343+00:00
-- url     : https://prove2.me/theorems/9e1844d7-a1c8-4c9e-a58a-e9e5db2715ba
-- title:
--   Limit of values in shrinking closed neighbourhoods lies in closed target
-- statement:
--   For any fixed positive radius, eventually all z n lie in its closed thickening. The limit belongs to every such thickening, hence the closed set.
-- source:
--   Kyprianou (2006), Theorem 3.3, delayed closed hitting approximation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.shrinkingClosedNeighbourhoodLimitV1
    (B : Set ℝ) (hB : IsClosed B) (z : ℕ → ℝ) (v : ℝ)
    (hz : Tendsto z atTop (𝓝 v))
    (hmem : ∀ n : ℕ, z n ∈ Metric.cthickening (1 / ((n : ℝ) + 1)) B) :
    v ∈ B := by
  sorry

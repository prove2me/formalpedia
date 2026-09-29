-- Prove2me | Theorems.Thm_MetricTSP_three_paths_separated
-- name    : MetricTSP.three_paths_separated
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T20:13:13.191506+00:00
-- url     : https://prove2.me/theorems/3c098cb1-584c-4f55-a074-f5a8605aee7d
-- title:
--   Distinct cities of the three-paths instance are at distance at least one
-- statement:
--   In the three-parallel-paths instance, any two distinct cities are at distance at least $1$: the cost is the shortest-path metric of an unweighted connected graph, where distinct vertices are at graph distance at least one. Formally this requires that the coordinates (path, position) determine the city, so equal coordinates force equality.
--
--   Combined with the degree constraints of the relaxation, this separation gives the positivity of the Held--Karp value of the instance ($\mathrm{hkValue} \ge n$), needed to make the integrality-gap ratio meaningful.
-- source:
--   Shortest-path distances of an unweighted connected graph take values in the positive integers on distinct vertices; see e.g. D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, CUP 2011, Section 11.2 (graph metrics).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths

namespace MetricTSP

theorem three_paths_separated (k : ℕ) (hk : 1 ≤ k) :
    ∀ u v : Fin (3*k+2), u ≠ v → (1 : ℝ) ≤ tpCost k u v := by sorry

end MetricTSP

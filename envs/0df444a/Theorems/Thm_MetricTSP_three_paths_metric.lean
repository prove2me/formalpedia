-- Prove2me | Theorems.Thm_MetricTSP_three_paths_metric
-- name    : MetricTSP.three_paths_metric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T20:12:08.984114+00:00
-- url     : https://prove2.me/theorems/1a1c39ef-d5f5-4894-ae90-2e0f2eae13e3
-- title:
--   The three-paths instance is a metric
-- statement:
--   The cost function of the three-parallel-paths instance is a genuine metric cost: it is symmetric, vanishes on the diagonal, and satisfies the triangle inequality.
--
--   The cost is defined by the closed-form shortest-path formula of the underlying graph (distance along a shared path, or through the nearer hub for cities on different paths), so the triangle inequality amounts to checking that the formula never beats a two-leg route --- a finite case analysis over which of the three pairs share a path, with each case a piece of linear arithmetic over positions.
-- source:
--   M. X. Goemans, Worst-case comparison of valid inequalities for the TSP, Mathematical Programming 69 (1995) 335-349 (the family is a shortest-path metric of an unweighted graph; shortest-path distances of any connected graph form a metric).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths

namespace MetricTSP

theorem three_paths_metric (k : ℕ) (hk : 1 ≤ k) : IsMetricCost (tpCost k) := by sorry

end MetricTSP

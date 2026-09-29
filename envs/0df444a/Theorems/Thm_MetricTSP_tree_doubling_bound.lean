-- Prove2me | Theorems.Thm_MetricTSP_tree_doubling_bound
-- name    : MetricTSP.tree_doubling_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:37:04.207683+00:00
-- url     : https://prove2.me/theorems/9101ce62-9fda-42a6-b8a3-002f2a6a0b18
-- title:
--   Tree doubling against the LP: $\mathrm{OPT} \le 2\,\mathrm{LP}$
-- statement:
--   For every metric TSP instance on $n \ge 3$ cities, the optimal tour costs at most twice the Held--Karp bound. The classical route: a scaled Held--Karp solution dominates a point of the spanning-tree polytope, so the minimum spanning tree costs at most the LP value; doubling the tree gives an Eulerian multigraph, and shortcutting the Eulerian traversal to a tour does not increase the cost, by the triangle inequality. A strict weakening of Wolsey's $\frac32$ bound, isolating the spanning-tree half of the argument from the parity/T-join half.
-- source:
--   Folklore (the LP-relative analysis of the double-tree algorithm); the spanning-tree vs. Held--Karp comparison is in Held--Karp, Oper. Res. 18 (1970) and Shmoys--Williamson, Inf. Process. Lett. 35 (1990), https://doi.org/10.1016/0020-0190(90)90028-V

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem tree_doubling_bound (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 2 * hkValue c := by sorry

end MetricTSP

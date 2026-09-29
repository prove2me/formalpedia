-- Prove2me | Theorems.Thm_MetricTSP_cheap_connected_subgraph
-- name    : MetricTSP.cheap_connected_subgraph
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T19:55:20.626403+00:00
-- url     : https://prove2.me/theorems/430cc641-48b5-42bc-8cdc-eedff010588e
-- title:
--   A connected subgraph no costlier than the Held--Karp objective
-- statement:
--   For every feasible point $x$ of the subtour-elimination (Held--Karp) relaxation on $n \ge 3$ cities with metric costs, there is a **connected spanning subgraph** of total edge cost at most the LP objective $\tfrac12 \sum_u \sum_v c(u,v)\,x_{uv}$ of $x$.
--
--   This is the fractional spanning-tree bound behind the tree-doubling and Christofides analyses: the minimum spanning tree costs at most the Held--Karp value. The classical argument scales $x$ by $\tfrac{n-1}{n}$ into the spanning-tree polytope; the elementary proof compares, at every cost threshold $t$, the number of expensive edges a minimum spanning tree can retain (at most the number of connected components of the cheap-pair graph, minus one, by the exchange argument) with the $x$-mass of the expensive pairs (at least as much, by the degree and cut constraints), and integrates over thresholds.
--
--   Combined with doubling-and-shortcutting this yields $\mathrm{OPT} \le 2\,\mathrm{LP}$, and it is one of the two halves of Wolsey's analysis of Christofides' algorithm against the LP.
-- source:
--   M. Held, R. M. Karp, The traveling-salesman problem and minimum spanning trees, Operations Research 18 (1970) 1138-1162 (Theorem 2: the gap between the minimum spanning 1-tree and the bound); D. B. Shmoys, D. P. Williamson, Analyzing the Held-Karp TSP bound: a monotonicity property with application, Information Processing Letters 35 (1990) 281-285, https://doi.org/10.1016/0020-0190(90)90028-V (MST is at most the Held--Karp bound); L. A. Wolsey, Heuristic analysis, linear programming and branch and bound, Mathematical Programming Study 13 (1980) 121-134, https://doi.org/10.1007/BFb0120913 (Section 3, the spanning-tree half of the Christofides analysis).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost

namespace MetricTSP

theorem cheap_connected_subgraph (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    ∃ G : SimpleGraph (Fin n), G.Connected ∧
      graphCost c G ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by sorry

end MetricTSP

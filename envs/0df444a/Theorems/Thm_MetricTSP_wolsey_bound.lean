-- Prove2me | Theorems.Thm_MetricTSP_wolsey_bound
-- name    : MetricTSP.wolsey_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:37:36.613348+00:00
-- url     : https://prove2.me/theorems/8a1ad8e8-8380-41d4-a1df-1e64268bf89c
-- title:
--   Wolsey: $\mathrm{OPT} \le \frac{3}{2}\,\mathrm{LP}$
-- statement:
--   (Wolsey 1980; rediscovered by Shmoys--Williamson 1990.) For every metric TSP instance on $n \ge 3$ cities, the optimal tour costs at most $\frac32$ times the Held--Karp bound — the integrality gap of the subtour-elimination LP is at most $\frac32$. The source proof runs Christofides' argument against the LP instead of against OPT: the minimum spanning tree costs at most the LP value, and the minimum matching on the odd-degree vertices of the tree costs at most half the LP value (via the T-join polyhedron), so tree plus matching, shortcut to a tour, costs at most $\frac32\,\mathrm{LP}$. This was the best known upper bound from 1980 until the $\frac32 - 10^{-36}$ of Karlin--Klein--Oveis Gharan (2022).
-- source:
--   Wolsey, Heuristic analysis, linear programming and branch and bound, Math. Prog. Study 13 (1980) 121-134, https://doi.org/10.1007/BFb0120913; Shmoys--Williamson, Analyzing the Held-Karp TSP bound, Inf. Process. Lett. 35 (1990), https://doi.org/10.1016/0020-0190(90)90028-V

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem wolsey_bound (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 3 / 2 * hkValue c := by sorry

end MetricTSP

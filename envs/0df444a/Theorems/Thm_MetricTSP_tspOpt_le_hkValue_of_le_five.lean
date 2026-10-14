-- Prove2me | Theorems.Thm_MetricTSP_tspOpt_le_hkValue_of_le_five
-- name    : MetricTSP.tspOpt_le_hkValue_of_le_five
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-13T03:39:42.861299+00:00
-- url     : https://prove2.me/theorems/b95b5136-a578-4a70-ab09-89c338b8ff0f
-- title:
--   No integrality gap up to five cities: $\mathrm{OPT} \le \mathrm{LP}$ for $n \le 5$
-- statement:
--   For every $n$ with $3 \le n \le 5$ and every metric cost function $c$ on $n$ cities (symmetric, zero on the diagonal, satisfying the triangle inequality), the optimal tour cost is at most the Held--Karp bound: $\mathrm{OPT}(c) \le \mathrm{LP}(c)$. Together with `held_karp_le_opt` this gives $\mathrm{OPT}(c) = \mathrm{LP}(c)$, so the subtour-elimination relaxation has no integrality gap on at most five cities. This also follows from a classical polyhedral fact: for $n \le 5$ the subtour-elimination polytope equals the convex hull of the tour incidence vectors, so equality holds for arbitrary symmetric edge costs, not only metric ones. For $n \ge 6$ the tour polytope is strictly contained in the subtour-elimination polytope, and Benoit--Boyd computed the exact metric integrality gap for every $n \le 10$.
-- source:
--   Classical: the subtour-elimination polytope equals the symmetric TSP polytope for $n \le 5$ and is strictly larger for $n \ge 6$, as stated in Letchford, Separating a superclass of comb inequalities in planar graphs, Math. Oper. Res. 25(3) (2000) 443-454, https://doi.org/10.1287/moor.25.3.443.12213, who attributes it to Grötschel--Padberg (1979); see Grötschel--Padberg, On the symmetric travelling salesman problem I: Inequalities and II: Lifting theorems and facets, Math. Programming 16 (1979) 265-280 and 281-302, https://doi.org/10.1007/BF01582116, https://doi.org/10.1007/BF01582117; exact gaps for $n \le 10$: Benoit--Boyd, Finding the exact integrality gap for small traveling salesman problems, Math. Oper. Res. 33(4) (2008) 921-931, https://doi.org/10.1287/moor.1080.0337

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem tspOpt_le_hkValue_of_le_five (n : ℕ) (hn : 3 ≤ n) (hn5 : n ≤ 5)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ hkValue c := by sorry

end MetricTSP

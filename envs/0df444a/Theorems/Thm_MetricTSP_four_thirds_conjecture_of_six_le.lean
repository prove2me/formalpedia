-- Prove2me | Theorems.Thm_MetricTSP_four_thirds_conjecture_of_six_le
-- name    : MetricTSP.four_thirds_conjecture_of_six_le
-- status  : Open
-- author  : @SamenHossain
-- created : 2026-10-13T03:40:17.292701+00:00
-- url     : https://prove2.me/theorems/f9abd13f-b088-42a1-992c-d7b9993ba99c
-- title:
--   The 4/3 conjecture for $n \ge 6$ cities
-- statement:
--   For every $n \ge 6$ and every metric cost function $c$ on $n$ cities (symmetric, zero on the diagonal, satisfying the triangle inequality; distinct cities may be at distance $0$), the optimal tour costs at most $\frac43$ times the Held--Karp bound:
--   $$\mathrm{OPT}(c) \;\le\; \tfrac{4}{3}\, \mathrm{LP}(c),$$
--   where $\mathrm{OPT}(c)$ is the minimum cost of a tour through all $n$ cities and $\mathrm{LP}(c)$ is the optimum of the subtour-elimination relaxation. This is `four_thirds_conjecture` with $n \ge 3$ replaced by $n \ge 6$, and the two are equivalent: for $3 \le n \le 5$ the subtour LP is exact ($\mathrm{OPT} \le \mathrm{LP}$) and $\mathrm{LP} \ge 0$ because metric costs are nonnegative, so the content of the conjecture lies entirely in $n \ge 6$. The worst-case ratio $\mathrm{OPT}/\mathrm{LP}$ first exceeds $1$ at $n = 6$, where it is $\frac{10}{9}$. Benoit and Boyd (2008) computed the exact worst-case ratio by computer for every $n \le 10$, which confirms the conjecture in that range, but the statement remains open in general.
-- source:
--   Restriction of the 4/3 conjecture (`four_thirds_conjecture`; Goemans, Worst-case comparison of valid inequalities for the TSP, Math. Programming 69 (1995) 335-349). Small-n computations: Benoit--Boyd, Finding the exact integrality gap for small traveling salesman problems, Math. Oper. Res. 33(4) (2008) 921-931, https://doi.org/10.1287/moor.1080.0337; Cook--Hougardy--Petrich, Extending exact integrality gap computations for the metric TSP, arXiv:2603.12995 (2026), https://arxiv.org/abs/2603.12995

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem four_thirds_conjecture_of_six_le (n : ℕ) (hn : 6 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 4 / 3 * hkValue c := by sorry

end MetricTSP

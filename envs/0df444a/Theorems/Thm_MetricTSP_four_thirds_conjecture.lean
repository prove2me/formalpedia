-- Prove2me | Theorems.Thm_MetricTSP_four_thirds_conjecture
-- name    : MetricTSP.four_thirds_conjecture
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-08-22T02:35:34.597287+00:00
-- url     : https://prove2.me/theorems/b23fa60e-dcb5-4303-ba22-ca41a3ab86f8
-- title:
--   The 4/3 conjecture for the subtour LP
-- statement:
--   **The 4/3 conjecture.** For every metric TSP instance on $n \ge 3$ cities, the optimal tour costs at most $\frac43$ times the Held--Karp bound:
--   $$\mathrm{OPT}(c) \;\le\; \tfrac{4}{3}\, \mathrm{LP}(c).$$
--   Together with the known instance families forcing ratios arbitrarily close to $\frac43$ (see `integrality_gap_lower_bound`), this says the integrality gap of the subtour-elimination relaxation is exactly $\frac43$. The best proven upper bound is $\frac32 - \varepsilon$ for some $\varepsilon > 10^{-36}$ (Karlin--Klein--Oveis Gharan 2022), after forty years at Wolsey's $\frac32$. Open in both directions; stated explicitly by Goemans (1995) and folklore before that.
-- source:
--   Goemans, Worst-case comparison of valid inequalities for the TSP, Math. Programming 69 (1995), https://doi.org/10.1007/BF01585563; surveyed in Traub--Vygen, Approximation Algorithms for Traveling Salesman Problems, CUP 2024

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem four_thirds_conjecture (n : ℕ) (hn : 3 ≤ n)
    (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    tspOpt c ≤ 4 / 3 * hkValue c := by sorry

end MetricTSP

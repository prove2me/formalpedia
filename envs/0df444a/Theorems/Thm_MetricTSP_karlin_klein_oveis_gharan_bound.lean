-- Prove2me | Theorems.Thm_MetricTSP_karlin_klein_oveis_gharan_bound
-- name    : MetricTSP.karlin_klein_oveis_gharan_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-08-31T12:50:20.269573+00:00
-- url     : https://prove2.me/theorems/c941cd75-0267-4b33-94dc-2adbcf22ef1b
-- title:
--   Integrality gap at most $3/2 - \varepsilon$ (Karlin–Klein–Oveis Gharan)
-- statement:
--   There is a constant $\varepsilon > 10^{-36}$ such that for every $n \ge 3$ and every metric cost $c$ on $n$ cities, the optimal tour cost is at most $(\frac{3}{2} - \varepsilon)$ times the Held–Karp bound: $\mathrm{OPT}(c) \le (\frac{3}{2} - \varepsilon)\,\mathrm{LP}(c)$. The single $\varepsilon$ is quantified before all instances. This is the first improvement over Wolsey's $3/2$ in forty years.
-- source:
--   A. Karlin, N. Klein, S. Oveis Gharan, A (slightly) improved bound on the integrality gap of the subtour LP for TSP, FOCS 2022, https://arxiv.org/abs/2105.10043, Theorem 1.1

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem karlin_klein_oveis_gharan_bound :
    ∃ ε : ℝ, 1 / 10 ^ 36 < ε ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ c : Fin n → Fin n → ℝ, IsMetricCost c →
        tspOpt c ≤ (3 / 2 - ε) * hkValue c := by sorry

end MetricTSP

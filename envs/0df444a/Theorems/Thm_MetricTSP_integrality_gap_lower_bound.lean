-- Prove2me | Theorems.Thm_MetricTSP_integrality_gap_lower_bound
-- name    : MetricTSP.integrality_gap_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:36:35.028515+00:00
-- url     : https://prove2.me/theorems/9bd098f2-fe21-454c-abae-0c2a954575f5
-- title:
--   Instance families force the gap to $4/3$
-- statement:
--   For every $\varepsilon > 0$ there is a metric TSP instance on some $n \ge 3$ cities with strictly positive Held--Karp bound and $\mathrm{OPT} \ge (\frac43 - \varepsilon)\,\mathrm{LP}$. The classical witnesses are the graph metrics of three parallel paths joined at their ends: the fractional solution with weight $\frac12$ on the connecting edges has cost about $n$, while every tour must traverse an extra path, costing about $\frac43 n$. Consequently the integrality gap of the subtour LP is at least $\frac43$, and the constant in the 4/3 conjecture cannot be improved.
-- source:
--   Folklore instance family; recorded e.g. in Goemans, Math. Programming 69 (1995), https://doi.org/10.1007/BF01585563, and Traub--Vygen, CUP 2024, Section 2.3

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem integrality_gap_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → Fin n → ℝ), 3 ≤ n ∧ IsMetricCost c ∧
      0 < hkValue c ∧ (4 / 3 - ε) * hkValue c ≤ tspOpt c := by sorry

end MetricTSP

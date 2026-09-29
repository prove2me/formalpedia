-- Prove2me | Theorems.Thm_MetricTSP_hk_value_le_of_feasible
-- name    : MetricTSP.hk_value_le_of_feasible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T19:20:34.839543+00:00
-- url     : https://prove2.me/theorems/a1cf9f92-760d-494d-90c0-e7eeabbfc68d
-- title:
--   Any feasible point bounds the Held--Karp value from above
-- statement:
--   The Held--Karp value $\mathrm{LP}(c)$ is defined as the infimum of the objective $\tfrac12 \sum_u \sum_v c(u,v)\,x_{uv}$ over all feasible points $x$ of the subtour-elimination relaxation. This lemma is the basic interface to that infimum: for a metric cost $c$, the objective of *any* feasible point bounds the value from above,
--   $$\mathrm{hkValue}(c) \;\le\; \tfrac12 \sum_u \sum_v c(u,v)\, x_{uv} \qquad \text{for every Held--Karp feasible } x.$$
--
--   The mathematical content is that the objective set is bounded below, so its infimum is a genuine lower bound: a metric cost is nonnegative (by symmetry and the triangle inequality, $0 = c(u,u) \le c(u,v) + c(v,u) = 2c(u,v)$), and feasible points are entrywise nonnegative, so every objective value is $\ge 0$.
--
--   This is the tool used whenever an explicit feasible solution is exhibited to bound the LP value from above --- for instance in the classical integrality-gap constructions for metric TSP.
-- source:
--   M. X. Goemans, Worst-case comparison of valid inequalities for the TSP, Mathematical Programming 69 (1995) 335-349, https://doi.org/10.1007/BF01585563 (upper bounds on the subtour LP value via explicit feasible solutions, used in the 4/3 lower-bound construction); D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press 2011, Section 11.2.

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem hk_value_le_of_feasible (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    hkValue c ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by sorry

end MetricTSP

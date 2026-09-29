-- Prove2me | Theorems.Thm_MetricTSP_tsp_opt_le_tour_cost
-- name    : MetricTSP.tsp_opt_le_tour_cost
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T19:54:54.450966+00:00
-- url     : https://prove2.me/theorems/f7b9a469-6e3f-43b2-b52a-ae89daa6a658
-- title:
--   The optimal value is at most any tour cost
-- statement:
--   The optimal tour value $\mathrm{tspOpt}(c)$ is defined as the infimum of $\mathrm{tourCost}(c, \pi)$ over all cyclic orderings $\pi$ of the cities. This lemma is the basic interface to that infimum: the value of **any** particular tour bounds the optimum from above,
--   $$\mathrm{tspOpt}(c) \;\le\; \mathrm{tourCost}(c, \pi) \qquad \text{for every ordering } \pi.$$
--
--   The mathematical content is that the set of tour costs is bounded below --- every tour cost is nonnegative because a metric cost is nonnegative ($0 = c(u,u) \le c(u,v) + c(v,u) = 2c(u,v)$ by the triangle inequality and symmetry) --- so the infimum over the reals is a genuine lower bound. It is the tool used whenever a tour is constructed explicitly (double-tree, Christofides, insertion heuristics) to conclude a bound on the optimum.
-- source:
--   D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press 2011, Section 2.4 (any constructed tour upper-bounds the optimum; used in the double-tree and Christofides analyses).

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem tsp_opt_le_tour_cost (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (π : Equiv.Perm (Fin n)) : tspOpt c ≤ tourCost c π := by sorry

end MetricTSP

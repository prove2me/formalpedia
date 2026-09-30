-- Prove2me | Theorems.Thm_InventoryControl_rq_discrete_cost_convex_R
-- name    : InventoryControl.rq_discrete_cost_convex_R
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:55:35.294983+00:00
-- url     : https://prove2.me/theorems/31c68b0f-8ccc-4a8f-98ff-eae7c6c0a80a
-- title:
--   The $(R,Q)$ cost is convex in the reorder point
-- statement:
--   Under a continuous review $(R,Q)$ policy with discrete lead-time demand, batch quantity
--   $Q \ge 1$, and costs $h > 0$, $b_1 > 0$, the total cost rate is a convex function of the
--   integral reorder point: for every $R \in \mathbb{Z}$,
--
--   $$ C(R+1, Q) - C(R, Q) \;\le\; C(R+2, Q) - C(R+1, Q). $$
--
--   The increments are $-b_1 + (h+b_1)S_3(R+1)$ by Eq. (5.60), and the ready rate $S_3$ is
--   nondecreasing in $R$ because each of its terms $\Pr[D(L) \le k - 1]$ is. Convexity is what
--   lets the optimal reorder point for a given $Q$ be characterized by a single comparison of
--   service levels, Eq. (5.61).
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 86, Sect. 5.9.1: 'Because the ready rate increases with the reorder point, it follows that C(R + 1) - C(R) is increasing with R, i.e., the cost is convex in the reorder point'

import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_cost_convex_R (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) (R : ℤ) :
    rqDiscreteCost D h b1 A μ (R + 1) Q - rqDiscreteCost D h b1 A μ R Q
      ≤ rqDiscreteCost D h b1 A μ (R + 2) Q - rqDiscreteCost D h b1 A μ (R + 1) Q := by sorry

end InventoryControl

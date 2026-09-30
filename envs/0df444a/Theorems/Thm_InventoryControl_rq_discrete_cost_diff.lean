-- Prove2me | Theorems.Thm_InventoryControl_rq_discrete_cost_diff
-- name    : InventoryControl.rq_discrete_cost_diff
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:54:48.593663+00:00
-- url     : https://prove2.me/theorems/d69a9f10-ef25-4b71-9d91-68ab5f74d8eb
-- title:
--   Eq. (5.60): $C(R+1) - C(R) = -b_1 + (h + b_1)\,S_3(R+1)$
-- statement:
--   Under a continuous review $(R,Q)$ policy with discrete lead-time demand, batch quantity
--   $Q \ge 1$, holding cost $h$ and shortage cost $b_1$ per unit and time unit, raising the reorder
--   point by one unit changes the total cost rate by
--
--   $$ C(R+1, Q) - C(R, Q) \;=\; -b_1 + (h + b_1)\,S_3(R+1), $$
--
--   where $S_3(R+1) = \Pr[IL > 0]$ is the ready rate at reorder point $R + 1$.
--
--   The book obtains this from the cost expression (5.57) and the shift relation (5.37),
--   $\Pr[IL = j \mid R] = \Pr[IL = j + 1 \mid R + 1]$. The ordering cost $A\mu/Q$ does not depend
--   on $R$ and cancels. Since the ready rate increases with $R$, the increments are nondecreasing
--   and the cost is convex in the reorder point, which is what makes the search "increase $R$ by
--   one unit at a time until the costs are increasing" exact.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 85, Sect. 5.9.1, Eq. (5.60)

import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_cost_diff (D : DiscreteDemand) (h b1 A μ : ℝ) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) :
    rqDiscreteCost D h b1 A μ (R + 1) Q - rqDiscreteCost D h b1 A μ R Q
      = -b1 + (h + b1) * rqDiscreteReadyRate D (R + 1) Q := by sorry

end InventoryControl

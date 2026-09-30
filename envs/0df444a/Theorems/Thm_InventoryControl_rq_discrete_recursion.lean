-- Prove2me | Theorems.Thm_InventoryControl_rq_discrete_recursion
-- name    : InventoryControl.rq_discrete_recursion
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:56:57.284776+00:00
-- url     : https://prove2.me/theorems/36eb65fb-d567-477a-8de5-8b3c00e8ee5e
-- title:
--   Eq. (6.6)-(6.7): the optimal reorder point and cost for $Q+1$ from those for $Q$
-- statement:
--   The Federgruen-Zheng recursion. Let $R^{*}(Q)$ be an optimal reorder point for batch quantity
--   $Q \ge 1$, under a discrete lead-time demand with finite mean, ordering cost $A$, demand rate
--   $\mu$, and costs $h > 0$, $b_1 > 0$. Define
--
--   $$ R^{*}(Q+1) \;=\; \begin{cases} R^{*}(Q) - 1 & \text{if } g(R^{*}(Q)) \le g(R^{*}(Q) + Q + 1),\\
--      R^{*}(Q) & \text{otherwise.}\end{cases} $$
--
--   Then $R^{*}(Q+1)$ is an optimal reorder point for batch quantity $Q + 1$, and its cost is
--
--   $$ C(Q+1) \;=\; C(Q)\,\frac{Q}{Q+1} \;+\; \min\big\{g(R^{*}(Q)),\, g(R^{*}(Q) + Q + 1)\big\}\,\frac{1}{Q+1}, $$
--
--   where $C(Q) = C(R^{*}(Q), Q)$ and $C(Q+1) = C(R^{*}(Q+1), Q+1)$.
--
--   The book's argument is that the optimal set of $Q$ consecutive inventory positions,
--   $\{R^{*}(Q)+1, \dots, R^{*}(Q)+Q\}$, grows into the optimal set of $Q+1$ positions by adding
--   whichever neighbour, $R^{*}(Q)$ on the left or $R^{*}(Q)+Q+1$ on the right, has the smaller
--   cost $g$; this rests on the convexity of $g$. The cost identity is then bookkeeping: the
--   window sum gains one term and the ordering cost $A\mu$ is spread over $Q+1$ instead of $Q$.
--
--   **Formalization Note** The statement holds for any optimal $R^{*}(Q)$, not only the one the
--   recursion generated, so the cost identity (6.7) shows that $C(Q+1)$ is the same whichever
--   optimal reorder point was chosen at stage $Q$.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 109, Sect. 6.1.1.1, Eq. (6.6) and Eq. (6.7)

import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_recursion (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) (Rstar : ℤ)
    (hR : ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ R Q) :
    let Rnext : ℤ := if sPolicyCost D h b1 Rstar ≤ sPolicyCost D h b1 (Rstar + Q + 1)
      then Rstar - 1 else Rstar
    (∀ R : ℤ, rqDiscreteCost D h b1 A μ Rnext (Q + 1) ≤ rqDiscreteCost D h b1 A μ R (Q + 1))
      ∧ rqDiscreteCost D h b1 A μ Rnext (Q + 1)
          = rqDiscreteCost D h b1 A μ Rstar Q * (Q / (Q + 1 : ℝ))
            + min (sPolicyCost D h b1 Rstar) (sPolicyCost D h b1 (Rstar + Q + 1))
                * (1 / (Q + 1 : ℝ)) := by sorry

end InventoryControl

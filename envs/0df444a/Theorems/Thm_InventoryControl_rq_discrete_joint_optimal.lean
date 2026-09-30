-- Prove2me | Theorems.Thm_InventoryControl_rq_discrete_joint_optimal
-- name    : InventoryControl.rq_discrete_joint_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:58:22.230652+00:00
-- url     : https://prove2.me/theorems/31d63e96-176b-4d98-8d33-67b3ca5e2c08
-- title:
--   Sect. 6.1.1.1: the first $Q$ with $C(Q+1) \ge C(Q)$, with its best $R$, is jointly optimal
-- statement:
--   The joint optimization of the reorder point and the batch quantity for discrete demand, the
--   capstone of Sect. 6.1.1.1 (Federgruen and Zheng, 1992).
--
--   A continuous review $(R,Q)$ policy controls an item with discrete lead-time demand $D(L)$ of
--   finite mean $\mu'$, average demand $\mu > 0$ per unit of time, ordering cost $A > 0$ per batch,
--   holding cost $h > 0$ and shortage cost $b_1 > 0$ per unit and time unit. With
--   $g(k) = -b_1(k - \mu') + (h+b_1)\sum_{j=1}^{k} j\Pr[D(L) = k-j]$ the cost rate of holding the
--   inventory position at $k$, the total average cost rate is
--
--   $$ C(R, Q) \;=\; \frac{A\mu}{Q} + \frac{1}{Q}\sum_{k=R+1}^{R+Q} g(k), $$
--
--   and $C(Q) = \min_R C(R,Q)$. Let $Q^{*} \ge 1$ be the smallest batch quantity with
--   $C(Q^{*}+1) \ge C(Q^{*})$, and let $R^{*}$ be an optimal reorder point for $Q^{*}$. Then
--
--   $$ C(R^{*}, Q^{*}) \;\le\; C(R, Q) \qquad\text{for every } R \in \mathbb{Z} \text{ and every } Q \ge 1 . $$
--
--   The point of the result is algorithmic: $C(Q)$ is not convex in $Q$ in any obvious sense, yet
--   the recursion (6.6)-(6.7) and the monotonicity of the marginal cost show that once the costs
--   stop decreasing they never decrease again, so the joint optimum is found by increasing $Q$ one
--   unit at a time and stopping at the first increase. The book applies the same idea to
--   $(s,S)$ policies in Sect. 6.1.1.2 and to normally distributed demand in Sect. 6.1.2.
--
--   **Formalization Note** $C(Q)$ is a function `CQ` constrained to be the least value of
--   $R \mapsto C(R,Q)$ for every $Q \ge 1$; $Q^{*}$ is characterized by the two stopping
--   conditions, and $R^{*}$ by optimality at $Q^{*}$. That such $C(Q)$, $Q^{*}$ and $R^{*}$ exist is
--   the content of two separate items of this mission.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 109, Sect. 6.1.1.1: 'Let Q* be the smallest Q such that C(Q + 1) >= C(Q). It follows from Eq. (6.7) that C(Q) >= C(Q*) for any Q >= Q*. Consequently, Q* and R*(Q*) provide the optimal solution'; the procedure is Federgruen and Zheng (1992)

import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_joint_optimal (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (hA : 0 < A) (hμ : 0 < μ)
    (CQ : ℕ → ℝ)
    (hCQ : ∀ Q : ℕ, 1 ≤ Q →
      IsLeast (Set.range fun R : ℤ => rqDiscreteCost D h b1 A μ R Q) (CQ Q))
    (Qstar : ℕ) (hQ1 : 1 ≤ Qstar) (hstop : CQ Qstar ≤ CQ (Qstar + 1))
    (hfirst : ∀ Q : ℕ, 1 ≤ Q → Q < Qstar → CQ (Q + 1) < CQ Q)
    (Rstar : ℤ)
    (hR : ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Qstar ≤ rqDiscreteCost D h b1 A μ R Qstar) :
    ∀ (R : ℤ) (Q : ℕ), 1 ≤ Q →
      rqDiscreteCost D h b1 A μ Rstar Qstar ≤ rqDiscreteCost D h b1 A μ R Q := by sorry

end InventoryControl

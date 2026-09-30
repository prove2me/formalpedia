-- Prove2me | Theorems.Thm_InventoryControl_rq_discrete_optimal_R
-- name    : InventoryControl.rq_discrete_optimal_R
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:56:04.323838+00:00
-- url     : https://prove2.me/theorems/aae587dc-c401-4b9a-92be-b3517b7afa94
-- title:
--   Eq. (5.61): the largest reorder point with $S_3(R) \le b_1/(h+b_1)$ is optimal
-- statement:
--   The discrete counterpart of the fill-rate rule for the reorder point. Under a continuous
--   review $(R,Q)$ policy with discrete lead-time demand, batch quantity $Q \ge 1$, and costs
--   $h > 0$, $b_1 > 0$, let $R^{*}$ be the largest reorder point whose ready rate does not exceed
--   $b_1/(h+b_1)$, that is
--
--   $$ S_3(R^{*}) \;\le\; \frac{b_1}{h + b_1} \;<\; S_3(R^{*} + 1). $$
--
--   Then $R^{*}$ minimizes the total cost rate $C(\cdot, Q)$ over all integral reorder points.
--
--   The two inequalities say, through Eq. (5.60), that moving from $R^{*}$ to $R^{*}+1$ increases
--   the cost while moving from $R^{*}-1$ to $R^{*}$ does not; with the cost convex in $R$ that
--   is optimality. The book notes that for pure Poisson demand the same statement holds with the
--   fill rate in place of the ready rate, since the two coincide.
--
--   **Formalization Note** $R^{*}$ is given together with the two service-level inequalities that
--   define it as the largest such reorder point; existence of such an $R^{*}$ (the ready rate
--   increases from $0$ to $1$) is not part of the claim.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 86, Sect. 5.9.1, Eq. (5.61): 'The optimal reorder point can be characterized as the largest reorder point giving a ready rate not higher than b1/(h + b1)'

import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_optimal_R (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) (Rstar : ℤ)
    (hlo : rqDiscreteReadyRate D Rstar Q ≤ b1 / (h + b1))
    (hhi : b1 / (h + b1) < rqDiscreteReadyRate D (Rstar + 1) Q) :
    ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ R Q := by sorry

end InventoryControl

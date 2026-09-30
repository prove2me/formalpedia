-- Prove2me | Theorems.Thm_InventoryControl_rq_discrete_marginal_mono
-- name    : InventoryControl.rq_discrete_marginal_mono
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:57:21.332564+00:00
-- url     : https://prove2.me/theorems/2025b529-5ea5-4108-a140-77e051027c6e
-- title:
--   $C(Q+1) \ge C(Q)$ iff $\min\{g(R^*(Q)), g(R^*(Q)+Q+1)\} \ge C(Q)$, and the minimum increases with $Q$
-- statement:
--   Two facts about the marginal cost of the $(Q+1)$-th unit of the batch. Under a discrete
--   lead-time demand with finite mean, ordering cost $A$, demand rate $\mu$, and costs $h > 0$,
--   $b_1 > 0$, let $R^{*}(Q)$ and $R^{*}(Q+1)$ be optimal reorder points for the batch quantities
--   $Q \ge 1$ and $Q + 1$, and write $m(Q) = \min\{g(R^{*}(Q)),\, g(R^{*}(Q) + Q + 1)\}$ for the
--   cost of the cheaper neighbour of the optimal window. Then
--
--   1. $C(R^{*}(Q+1), Q+1) \ge C(R^{*}(Q), Q)$ if and only if $m(Q) \ge C(R^{*}(Q), Q)$;
--   2. $m(Q) \le m(Q+1)$.
--
--   The first is read off Eq. (6.7): $C(Q+1)$ is a weighted average of $C(Q)$ and $m(Q)$ with
--   weights $Q/(Q+1)$ and $1/(Q+1)$, so it exceeds $C(Q)$ exactly when $m(Q)$ does. The second is
--   the book's "obvious" step: as the optimal window grows, the neighbours it has not yet absorbed
--   lie further out on a convex $g$ and can only cost more. Together they are what makes the
--   stopping rule of Sect. 6.1.1.1 correct.
--
--   **Formalization Note** The reorder points may be any optimal ones for their batch quantities;
--   by Eq. (6.7) the value $m(Q)$ does not depend on the choice.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 109, Sect. 6.1.1.1, the two sentences after Eq. (6.7): 'It is evident from Eq. (6.7) that C(Q + 1) >= C(Q) if and only if min{g(R*(Q)), g(R*(Q) + Q + 1)} >= C(Q). Furthermore, it is obvious that min{g(R*(Q)), g(R*(Q) + Q + 1)} is increasing with Q'

import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_marginal_mono (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) (Rstar Rnext : ℤ)
    (hR : ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ R Q)
    (hR' : ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rnext (Q + 1) ≤ rqDiscreteCost D h b1 A μ R (Q + 1)) :
    (rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ Rnext (Q + 1)
        ↔ rqDiscreteCost D h b1 A μ Rstar Q
            ≤ min (sPolicyCost D h b1 Rstar) (sPolicyCost D h b1 (Rstar + Q + 1)))
      ∧ min (sPolicyCost D h b1 Rstar) (sPolicyCost D h b1 (Rstar + Q + 1))
          ≤ min (sPolicyCost D h b1 Rnext) (sPolicyCost D h b1 (Rnext + (Q + 1) + 1)) := by sorry

end InventoryControl

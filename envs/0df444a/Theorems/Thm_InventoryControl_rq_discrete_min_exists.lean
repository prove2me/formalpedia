-- Prove2me | Theorems.Thm_InventoryControl_rq_discrete_min_exists
-- name    : InventoryControl.rq_discrete_min_exists
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:56:35.241024+00:00
-- url     : https://prove2.me/theorems/ac24f612-250c-4e54-862e-3013aa6cf5f2
-- title:
--   Eq. (6.5): $C(Q) = \min_R C(R,Q)$ is attained
-- statement:
--   For every batch quantity $Q \ge 1$ there is a reorder point $R^{*}$ that minimizes the total
--   cost rate $C(\cdot, Q)$ over all of $\mathbb{Z}$:
--
--   $$ \exists\, R^{*} \in \mathbb{Z} \quad\text{such that}\quad C(R^{*}, Q) \le C(R, Q)
--      \ \text{ for every } R \in \mathbb{Z}, $$
--
--   for a discrete lead-time demand with finite mean and costs $h > 0$, $b_1 > 0$.
--
--   Equation (6.5) defines $C(Q)$ as a minimum over $R$ and the algorithm of Sect. 6.1.1.1
--   manipulates $R^{*}(Q)$ throughout; the minimum exists because $g(k) \to \infty$ as
--   $|k| \to \infty$, so the average of $g$ over the window $\{R+1, \dots, R+Q\}$ also tends to
--   infinity in both directions and a lowest value is attained. Establishing this separately
--   keeps the later statements free of an infimum that could be junk.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 108, Sect. 6.1.1.1, Eq. (6.5): 'Let us now define C(Q) as C(Q) = min_R {C(R, Q)}'; the minimum is written without comment, which presupposes this

import Definitions.Def_InventoryControl_rqDiscrete

namespace InventoryControl

theorem rq_discrete_min_exists (D : DiscreteDemand) (h b1 A μ : ℝ) (hh : 0 < h) (hb : 0 < b1)
    (Q : ℕ) (hQ : 0 < Q) :
    ∃ Rstar : ℤ, ∀ R : ℤ, rqDiscreteCost D h b1 A μ Rstar Q ≤ rqDiscreteCost D h b1 A μ R Q := by sorry

end InventoryControl

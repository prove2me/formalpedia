-- Prove2me | Theorems.Thm_InventoryControl_rq_ready_rate
-- name    : InventoryControl.rq_ready_rate
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:44:40.299533+00:00
-- url     : https://prove2.me/theorems/c9925b70-14ba-4fc3-a92f-76f81ae5e31a
-- title:
--   Eq. (5.52): $S_2 = S_3 = 1 - \frac{\sigma'}{Q}\left[G\left(\frac{R-\mu'}{\sigma'}\right) - G\left(\frac{R+Q-\mu'}{\sigma'}\right)\right]$
-- statement:
--   For continuous normally distributed demand the fill rate $S_2$ (fraction of demand met from
--   stock on hand) and the ready rate $S_3$ (fraction of time with positive stock) coincide, and
--   both equal the probability of positive stock, $1 - F(0)$. Under a continuous review $(R,Q)$
--   policy with $Q > 0$, mean lead-time demand $\mu'$ and standard deviation $\sigma' > 0$,
--
--   $$ S_2 \;=\; S_3 \;=\; \Pr[IL > 0] \;=\; 1 - \frac{\sigma'}{Q}\left[G\!\left(\frac{R - \mu'}{\sigma'}\right) - G\!\left(\frac{R + Q - \mu'}{\sigma'}\right)\right]. $$
--
--   This is the formula a planner inverts to find the smallest reorder point meeting a prescribed
--   fill rate (the book's bisection search), and it is the quantity that Eq. (5.67) later ties to
--   the cost parameters: at the cost-optimal reorder point it equals $b_1/(h + b_1)$.
--
--   **Formalization Note** The ready rate is defined directly as the `rqLevel`-measure of
--   $(0, \infty)$; that it is $1 - F(0)$ is part of the claim.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 82, Sect. 5.7.2, Eq. (5.52)

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_ready_rate (R Q m s : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    rqReadyRate R Q m s
      = 1 - s / Q * (normalLoss ((R - m) / s) - normalLoss ((R + Q - m) / s)) := by sorry

end InventoryControl

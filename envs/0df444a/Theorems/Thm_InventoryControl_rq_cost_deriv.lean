-- Prove2me | Theorems.Thm_InventoryControl_rq_cost_deriv
-- name    : InventoryControl.rq_cost_deriv
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:50:33.576248+00:00
-- url     : https://prove2.me/theorems/c6f81487-2f48-4e8b-906c-89a13bbecb32
-- title:
--   Eq. (5.66): $\frac{dC}{dR} = -b_1 + (h + b_1)\,S_2$
-- statement:
--   The expected cost rate $C(R)$ of a continuous review $(R,Q)$ policy is differentiable in the
--   reorder point, and its derivative is expressed through the service level. With $h > 0$,
--   $b_1 > 0$, $Q > 0$ and normal lead-time demand ($\sigma' > 0$),
--
--   $$ \frac{\mathrm{d}C}{\mathrm{d}R} \;=\; -b_1 + (h + b_1)\,S_2(R), $$
--
--   where $S_2(R) = S_3(R) = \Pr[IL > 0]$ is the fill rate (equivalently the ready rate) at reorder
--   point $R$.
--
--   The book derives it from the closed form (5.65), the fill rate formula (5.52) and $H' = -G$:
--   the loss-function terms produced by differentiating $H$ are exactly $\sigma'[G(\cdot) -
--   G(\cdot)]$, which is $Q(1 - S_2)$. The identity has an immediate reading: raising the reorder
--   point by one unit costs $h$ per time unit in holding when the stock is positive and saves
--   $b_1$ when it is not, and the fill rate is the fraction of time the stock is positive.
--
--   **Formalization Note** The statement is a `HasDerivAt` of $R \mapsto$ `rqCost h b1 R Q m s`
--   at each $R$, with the derivative written through `rqReadyRate`.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 86, Sect. 5.9.2, Eq. (5.66)

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_cost_deriv (h b1 R Q m s : ℝ) (hh : 0 < h) (hb : 0 < b1) (hQ : 0 < Q) (hs : 0 < s) :
    HasDerivAt (fun R => rqCost h b1 R Q m s) (-b1 + (h + b1) * rqReadyRate R Q m s) R := by sorry

end InventoryControl

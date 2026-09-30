-- Prove2me | Theorems.Thm_InventoryControl_rq_cost_convex
-- name    : InventoryControl.rq_cost_convex
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:50:53.177232+00:00
-- url     : https://prove2.me/theorems/f6f7a067-a16e-43de-8c6c-5c9aca7b320f
-- title:
--   The expected cost is a convex function of the reorder point
-- statement:
--   Under a continuous review $(R,Q)$ policy with $Q > 0$, holding cost $h > 0$, backorder cost
--   $b_1 > 0$ and normal lead-time demand ($\sigma' > 0$), the expected cost rate
--   $R \mapsto C(R)$ is a convex function of the reorder point on the whole real line.
--
--   The book's reason is Eq. (5.66): the derivative $-b_1 + (h + b_1)S_2(R)$ is increasing in $R$
--   because the fill rate is. Convexity is what makes the stationarity condition (5.67) sufficient
--   for optimality and not merely necessary, and it is the property the joint optimization of
--   Chapter 6 relies on when it solves $\partial C/\partial R = 0$ for $R$ at fixed $Q$.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 86, Sect. 5.9.2, the sentence after Eq. (5.66): 'Since dC/dR is increasing with R, C is a convex function of R'

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_cost_convex (h b1 Q m s : ℝ) (hh : 0 < h) (hb : 0 < b1) (hQ : 0 < Q) (hs : 0 < s) :
    ConvexOn ℝ Set.univ (fun R => rqCost h b1 R Q m s) := by sorry

end InventoryControl

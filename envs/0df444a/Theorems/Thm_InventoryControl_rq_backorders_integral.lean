-- Prove2me | Theorems.Thm_InventoryControl_rq_backorders_integral
-- name    : InventoryControl.rq_backorders_integral
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:47:30.77703+00:00
-- url     : https://prove2.me/theorems/3a5532d9-6ef1-4746-a741-a02878f84bcd
-- title:
--   Eq. (5.63): $\mathbb{E}(IL)^{-} = \int_{-\infty}^{0} F(x)\,dx$
-- statement:
--   The expected backorder level equals the integral of the inventory level's distribution
--   function over the negative half-line. Under a continuous review $(R,Q)$ policy with $Q > 0$
--   and normal lead-time demand ($\sigma' > 0$),
--
--   $$ \mathbb{E}(IL)^{-} \;=\; \mathbb{E}\big[\max(-IL, 0)\big] \;=\; \int_{-\infty}^{0} F(x)\,\mathrm{d}x . $$
--
--   The book proves it by writing $-u = \int_u^0\mathrm{d}x$ for $u < 0$ and exchanging the order
--   of integration. It converts the backorder term of the cost into an integral of the closed form
--   (5.42), which is what produces the second loss function $H$ in Eq. (5.65).
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 85, Sect. 5.9.2, Eq. (5.63)

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_backorders_integral (R Q m s : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    ∫ x, max (-x) 0 ∂(rqLevel R Q m s) = ∫ x in Set.Iic 0, rqCDF R Q m s x := by sorry

end InventoryControl

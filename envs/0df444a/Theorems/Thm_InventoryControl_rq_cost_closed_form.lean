-- Prove2me | Theorems.Thm_InventoryControl_rq_cost_closed_form
-- name    : InventoryControl.rq_cost_closed_form
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:49:44.725587+00:00
-- url     : https://prove2.me/theorems/6518e9e2-9c1c-445d-8418-46f883ff1ced
-- title:
--   Eq. (5.65): $C = h(R + Q/2 - \mu') + (h+b_1)\frac{\sigma'^2}{Q}\left[H\left(\frac{R-\mu'}{\sigma'}\right) - H\left(\frac{R+Q-\mu'}{\sigma'}\right)\right]$
-- statement:
--   The expected holding-plus-backorder cost rate of a continuous review $(R,Q)$ policy has a
--   closed form. With holding cost $h > 0$ per unit and time unit, backorder cost $b_1 > 0$ per unit
--   and time unit, batch quantity $Q > 0$, and normal lead-time demand with mean $\mu'$ and
--   standard deviation $\sigma' > 0$,
--
--   $$ C(R) \;=\; \mathbb{E}\big[h\,(IL)^{+} + b_1\,(IL)^{-}\big]
--      \;=\; h\Big(R + \frac{Q}{2} - \mu'\Big) + (h + b_1)\,\frac{\sigma'^{2}}{Q}\left[H\!\left(\frac{R - \mu'}{\sigma'}\right) - H\!\left(\frac{R + Q - \mu'}{\sigma'}\right)\right], $$
--
--   where $H(x) = \int_x^{\infty} G(v)\,\mathrm{d}v$ is the second loss function of Eq. (5.64).
--
--   The book reaches it in three lines (Eq. 5.62): it writes the cost as
--   $h\,\mathbb{E}(IL) + (h + b_1)\,\mathbb{E}(IL)^{-}$ using $x^{+} - x^{-} = x$, replaces
--   $\mathbb{E}(IL)^{-}$ by $\int_{-\infty}^{0}F(x)\,\mathrm{d}x$, substitutes the closed form
--   (5.42) and changes the order of integration. This is the expression that Chapter 6 adds an
--   ordering cost to in its joint optimization of $R$ and $Q$, Eq. (6.10).
--
--   **Formalization Note** $C(R)$ is `rqCost h b1 R Q m s`, a Bochner integral against the law
--   `rqLevel R Q m s`; integrability of the integrand is a separate theorem of this mission.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, pp. 85-86, Sect. 5.9.2, Eq. (5.62) and Eq. (5.65)

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_cost_closed_form (h b1 R Q m s : ℝ) (hh : 0 < h) (hb : 0 < b1) (hQ : 0 < Q)
    (hs : 0 < s) :
    rqCost h b1 R Q m s
      = h * (R + Q / 2 - m)
        + (h + b1) * (s ^ 2 / Q) * (normalLossH ((R - m) / s) - normalLossH ((R + Q - m) / s)) := by sorry

end InventoryControl

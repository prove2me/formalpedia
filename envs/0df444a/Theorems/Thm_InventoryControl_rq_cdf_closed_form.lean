-- Prove2me | Theorems.Thm_InventoryControl_rq_cdf_closed_form
-- name    : InventoryControl.rq_cdf_closed_form
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:43:34.90793+00:00
-- url     : https://prove2.me/theorems/91891b4c-797c-49eb-91ba-1a4d03ad0302
-- title:
--   Eq. (5.42): $F(x) = \frac{\sigma'}{Q}\left[G\left(\frac{R-x-\mu'}{\sigma'}\right) - G\left(\frac{R+Q-x-\mu'}{\sigma'}\right)\right]$
-- statement:
--   The distribution function of the inventory level under a continuous review $(R,Q)$ policy
--   with $Q > 0$ and normal lead-time demand of mean $\mu'$ and standard deviation $\sigma' > 0$
--   has the closed form
--
--   $$ F(x) \;=\; \frac{\sigma'}{Q}\left[G\!\left(\frac{R - x - \mu'}{\sigma'}\right) - G\!\left(\frac{R + Q - x - \mu'}{\sigma'}\right)\right], $$
--
--   where $G$ is the standard normal loss function of Eq. (5.40).
--
--   The book obtains it by writing the integrand of Eq. (5.39) as $-G'$ using Eq. (5.41) and
--   integrating over the uniform inventory position. It is the workhorse of the chapter: the
--   service levels of Sect. 5.7.2, the backorder cost of Sect. 5.9.2 and the periodic-review fill
--   rate of Sect. 5.12.4 are all evaluated from it, and it is why the loss function is tabulated
--   in the book's Appendix 2.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 76, Sect. 5.3.4, Eq. (5.42)

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_cdf_closed_form (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    rqCDF R Q m s x
      = s / Q * (normalLoss ((R - x - m) / s) - normalLoss ((R + Q - x - m) / s)) := by sorry

end InventoryControl

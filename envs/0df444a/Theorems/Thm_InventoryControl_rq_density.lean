-- Prove2me | Theorems.Thm_InventoryControl_rq_density
-- name    : InventoryControl.rq_density
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:44:07.6089+00:00
-- url     : https://prove2.me/theorems/4e4a7395-7c89-407d-b271-0c27b40d19a8
-- title:
--   Eq. (5.43): $f(x) = \frac{1}{Q}\left[\Phi\left(\frac{R+Q-x-\mu'}{\sigma'}\right) - \Phi\left(\frac{R-x-\mu'}{\sigma'}\right)\right]$
-- statement:
--   The inventory level under a continuous review $(R,Q)$ policy with $Q > 0$ and normal lead-time
--   demand ($\sigma' > 0$) has a density: its distribution function $F$ is differentiable at every
--   $x$, with
--
--   $$ f(x) \;=\; F'(x) \;=\; \frac{1}{Q}\left[\Phi\!\left(\frac{R + Q - x - \mu'}{\sigma'}\right) - \Phi\!\left(\frac{R - x - \mu'}{\sigma'}\right)\right]. $$
--
--   The density is the average, over the uniform inventory position $u \in [R, R+Q]$, of the
--   normal density of $u - D(L)$ at $x$; the book writes it as
--   $\frac{1}{Q}\int_R^{R+Q}\frac{1}{\sigma'}\varphi\big(\frac{u-x-\mu'}{\sigma'}\big)\mathrm{d}u$
--   and evaluates the integral. Letting $Q \to 0$ recovers the normal density of an $S$ policy,
--   Eq. (5.45).
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 76, Sect. 5.3.4, Eq. (5.43)

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_density (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    HasDerivAt (rqCDF R Q m s)
      (1 / Q * (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) ((R + Q - x - m) / s)
                 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) ((R - x - m) / s))) x := by sorry

end InventoryControl

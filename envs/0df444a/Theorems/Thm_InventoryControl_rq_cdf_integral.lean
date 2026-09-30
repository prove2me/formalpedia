-- Prove2me | Theorems.Thm_InventoryControl_rq_cdf_integral
-- name    : InventoryControl.rq_cdf_integral
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:43:02.978486+00:00
-- url     : https://prove2.me/theorems/78a52d77-2c76-4144-be82-903b1c494077
-- title:
--   Eq. (5.39): $F(x) = \frac{1}{Q}\int_R^{R+Q}\left[1 - \Phi\left(\frac{u-x-\mu'}{\sigma'}\right)\right]du$
-- statement:
--   Under a continuous review $(R,Q)$ policy with $Q > 0$, an inventory position uniform on
--   $[R, R+Q]$, and independent normal lead-time demand with mean $\mu'$ and standard deviation
--   $\sigma' > 0$, the distribution function of the inventory level $IL = IP - D(L)$ is
--
--   $$ F(x) \;=\; \Pr[IL \le x] \;=\; \frac{1}{Q}\int_R^{R+Q}\left[1 - \Phi\!\left(\frac{u - x - \mu'}{\sigma'}\right)\right]\mathrm{d}u . $$
--
--   The book's justification is one sentence: given the inventory position $u$ at time $t$, the
--   inventory level at time $t + L$ is at most $x$ exactly when the lead-time demand is at least
--   $u - x$, whose probability is $1 - \Phi((u - x - \mu')/\sigma')$; averaging over the uniform
--   position gives the formula. This is the conditioning step that every later closed form rests
--   on.
--
--   **Formalization Note** The left-hand side is the measure of $(-\infty, x]$ under `rqLevel`, the
--   pushforward of the product of the uniform and normal laws under subtraction, so the statement
--   is a genuine Fubini-type identity rather than a definition.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 75, Sect. 5.3.4, Eq. (5.39)

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem rq_cdf_integral (R Q m s x : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    rqCDF R Q m s x
      = (1 / Q) * ∫ u in R..R + Q,
          (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) ((u - x - m) / s)) := by sorry

end InventoryControl

-- Prove2me | Theorems.Thm_InventoryControl_normal_loss_deriv
-- name    : InventoryControl.normal_loss_deriv
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:41:25.476199+00:00
-- url     : https://prove2.me/theorems/2ecc9eef-8880-46b3-ac62-9ebc2fb95163
-- title:
--   Eq. (5.41): $G'(x) = \Phi(x) - 1$
-- statement:
--   The standard normal loss function $G(x) = \int_x^{\infty}(v-x)\varphi(v)\,\mathrm{d}v$ is
--   differentiable at every real $x$, with
--
--   $$ G'(x) \;=\; \Phi(x) - 1 , $$
--
--   where $\Phi$ is the standard normal distribution function.
--
--   This is the derivative the whole chapter differentiates with: the density of the inventory level
--   (Eq. 5.43), the fill rate's monotonicity in $R$ (Sect. 5.7.2), and the first-order condition
--   for the reorder point (Eq. 5.66) are all obtained by differentiating $G$. Since $\Phi(x) - 1$
--   is negative and increasing, $G$ is decreasing and convex, which is stated separately.
--
--   **Formalization Note** $G$ is `normalLoss` from the newsboy definitions and $\Phi$ is the
--   distribution function of `gaussianReal 0 1`; the statement is a `HasDerivAt`.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 76, Eq. (5.41): 'Note that G'(x) = Phi(x) - 1'

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem normal_loss_deriv (x : ℝ) :
    HasDerivAt normalLoss (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x - 1) x := by sorry

end InventoryControl

-- Prove2me | Theorems.Thm_InventoryControl_normal_lossH_closed_form
-- name    : InventoryControl.normal_lossH_closed_form
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T23:48:03.251587+00:00
-- url     : https://prove2.me/theorems/4bf6f478-2109-4c22-a0df-307bad24d918
-- title:
--   Eq. (5.64): $H(x) = \tfrac12\left[(x^2+1)(1-\Phi(x)) - x\varphi(x)\right]$
-- statement:
--   The second loss function
--
--   $$ H(x) \;=\; \int_x^{\infty} G(v)\,\mathrm{d}v $$
--
--   has the closed form
--
--   $$ H(x) \;=\; \frac{1}{2}\Big[(x^{2} + 1)\big(1 - \Phi(x)\big) - x\,\varphi(x)\Big], $$
--
--   with $\varphi$ and $\Phi$ the standard normal density and distribution function. (The book
--   notes that the literature often uses $\bar H(x) = 2H(x)$ instead.)
--
--   $H$ is tabulated in the book's Appendix 2 alongside $G$, and it is the function through which
--   the expected backorder level of an $(R,Q)$ policy is expressed in Eq. (5.65) and again in the
--   periodic-review fill rate of Eq. (5.86) and the joint optimization of Chapter 6.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 86, Sect. 5.9.2, Eq. (5.64), and Appendix 2 p. 242

import Definitions.Def_InventoryControl_rq

namespace InventoryControl

theorem normal_lossH_closed_form (x : ℝ) :
    normalLossH x
      = ((x ^ 2 + 1) * (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x)
          - x * ProbabilityTheory.gaussianPDFReal 0 1 x) / 2 := by sorry

end InventoryControl

-- Prove2me | Theorems.Thm_LostSalesRQ_endpoint_low_price_anchor
-- name    : LostSalesRQ.endpoint_low_price_anchor
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:31:29.24601+00:00
-- url     : https://prove2.me/theorems/a6c72ae4-985f-459f-9707-c6e049e1e05f
-- title:
--   Lemma 2(i): a common starting penalty for small base-stock levels
-- statement:
--   Fix $\mu>0$ and define
--   $$\eta^\circ=A_1=1+\mu^{-1},\qquad a^\circ=1+\frac{2-e^{-\mu}}{\mu},\qquad g^\circ=1+\frac{1-e^{-\mu}}{\mu}.$$
--   Then $a^\circ=\alpha_\mu(\eta^\circ)$, $\mathcal L_\mu(a^\circ)\ge g^\circ$, and
--   $$\max\{L_1(a^\circ),L_2(a^\circ)\}<\tfrac54\,g^\circ\quad(\mu>0),\qquad L_3(a^\circ)<\tfrac75\,g^\circ\quad(\mu\ge2).$$
--
--   Since $5/4$ and $7/5$ are below $\sqrt2$, base stocks one and two (and three when $\mu\ge2$) all cost less than $\sqrt2\,\mathcal L_\mu(a^\circ)$ at this single penalty.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Lemma 2(i), eq. (17) (p. 17); proof in Appendix E (pp. A9-A10).

import Definitions.Def_LostSalesRQ_lower_curve
import Definitions.Def_LostSalesRQ_poisson_process

namespace LostSalesRQ

theorem endpoint_low_price_anchor (μ : ℝ) (hμ : 0 < μ) :
    erlangNormalizer μ 1 = 1 + μ⁻¹ ∧
    calibratedPenalty μ (1 + μ⁻¹) = 1 + (2 - Real.exp (-μ)) / μ ∧
    1 + (1 - Real.exp (-μ)) / μ ≤ lowerCurve μ (1 + (2 - Real.exp (-μ)) / μ) ∧
    max (baseStockCost μ (1 + (2 - Real.exp (-μ)) / μ) 1)
        (baseStockCost μ (1 + (2 - Real.exp (-μ)) / μ) 2) <
      5 / 4 * (1 + (1 - Real.exp (-μ)) / μ) ∧
    (2 ≤ μ → baseStockCost μ (1 + (2 - Real.exp (-μ)) / μ) 3 <
      7 / 5 * (1 + (1 - Real.exp (-μ)) / μ)) := by sorry

end LostSalesRQ

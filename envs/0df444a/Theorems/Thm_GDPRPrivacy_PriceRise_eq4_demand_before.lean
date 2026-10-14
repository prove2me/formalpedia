-- Prove2me | Theorems.Thm_GDPRPrivacy_PriceRise_eq4_demand_before
-- name    : GDPRPrivacy.PriceRise.eq4_demand_before
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:21.470994+00:00
-- url     : https://prove2.me/theorems/2a64d389-3fee-410e-bdfe-151fad0c6e0c
-- title:
--   Display (4), p. 11 — demand before the GDPR, D̂(p̂) = (1+x−p̂)²/2 on (x, 1+x) and 1 − (1−x+p̂)²/2 on [x−1, x]
-- statement:
--   Let $0 < x < 1$ be the opt-in benefit. Before the GDPR a consumer of type $(v,c)$, uniform on $[0,1]^2$, buys at price $\hat p$ iff $c \le v + x - \hat p$; let $\widehat D(\hat p)$ be the mass of buyers. Then
--   $$\widehat D(\hat p) = \begin{cases} \dfrac{(1 + x - \hat p)^2}{2} & \text{if } x < \hat p < 1 + x,\\[2mm] 1 - \dfrac{(1 - x + \hat p)^2}{2} & \text{if } x - 1 \le \hat p \le x. \end{cases}$$
--
--   This is the demand curve the firm faces before the GDPR. Combined with $\widehat\Pi(\hat p) = (\hat p + \alpha)\widehat D(\hat p)$ it gives the two profit pieces $\widehat\Pi_h$, $\widehat\Pi_l$ that the paper maximizes.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), p. 11, display (4)

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.PriceRise

theorem eq4_demand_before (x p : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (x < p → p < 1 + x → demandBefore x p = (1 + x - p) ^ 2 / 2) ∧
    (x - 1 ≤ p → p ≤ x → demandBefore x p = 1 - (1 - x + p) ^ 2 / 2) := by sorry

end GDPRPrivacy.PriceRise

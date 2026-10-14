-- Prove2me | Theorems.Thm_GDPRPrivacy_PriceRise_eq5_demand_in
-- name    : GDPRPrivacy.PriceRise.eq5_demand_in
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:19.004879+00:00
-- url     : https://prove2.me/theorems/3a786b24-dcc4-4bb0-8f77-f9d81c6f5dd0
-- title:
--   Display (5), p. 14 — the opt-in demand after the GDPR, D̃_S(p̃), in three price ranges
-- statement:
--   Let $0 < x < 1$. After the GDPR a consumer of type $(v,c)$, uniform on $[0,1]^2$, opts in at price $\tilde p$ iff $c \le v + x - \tilde p$ and $c \le x$; let $\widetilde D_S(\tilde p)$ be the mass of opt-in consumers. Then
--   $$\widetilde D_S(\tilde p) = \begin{cases} \dfrac{(1 + x - \tilde p)^2}{2} & \text{if } 1 < \tilde p < 1 + x,\\[2mm] \dfrac{x^2}{2} + x(1 - \tilde p) & \text{if } x < \tilde p \le 1,\\[2mm] x - \dfrac{\tilde p^2}{2} & \text{if } 0 \le \tilde p \le x. \end{cases}$$
--
--   Together with display (6) this gives the post-GDPR total demand (7) and the profit $\widetilde\Pi(\tilde p) = \tilde p\,\widetilde D(\tilde p) + \alpha\,\widetilde D_S(\tilde p)$; the data revenue depends only on this opt-in demand.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), p. 14, display (5)

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.PriceRise

theorem eq5_demand_in (x p : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (1 < p → p < 1 + x → demandIn x p = (1 + x - p) ^ 2 / 2) ∧
    (x < p → p ≤ 1 → demandIn x p = x ^ 2 / 2 + x * (1 - p)) ∧
    (0 ≤ p → p ≤ x → demandIn x p = x - p ^ 2 / 2) := by sorry

end GDPRPrivacy.PriceRise

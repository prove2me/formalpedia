-- Prove2me | Theorems.Thm_GDPRPrivacy_PriceRise_eq6_demand_out
-- name    : GDPRPrivacy.PriceRise.eq6_demand_out
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:17.507715+00:00
-- url     : https://prove2.me/theorems/3d7bc3fb-d593-41c1-980d-1cd7b9594eab
-- title:
--   Display (6), p. 14 — the opt-out demand, D̃_N(p̃) = (1−x)(1−p̃) for 0 ≤ p̃ ≤ 1 and 0 for 1 < p̃ < 1+x
-- statement:
--   Let $0 < x < 1$. After the GDPR a consumer of type $(v,c)$, uniform on $[0,1]^2$, opts out at price $\tilde p$ iff $v \ge \tilde p$ and $c > x$; let $\widetilde D_N(\tilde p)$ be the mass of opt-out consumers. Then
--   $$\widetilde D_N(\tilde p) = \begin{cases} 0 & \text{if } 1 < \tilde p < 1 + x,\\ (1 - x)(1 - \tilde p) & \text{if } 0 \le \tilde p \le 1. \end{cases}$$
--
--   The opt-out option is what the GDPR adds: these are the buyers whose privacy cost exceeds the opt-in benefit. They pay the price but generate no data revenue, and for prices above $1$ there are none.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), p. 14, display (6) and the sentence before it

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.PriceRise

theorem eq6_demand_out (x p : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (1 < p → p < 1 + x → demandOut x p = 0) ∧
    (0 ≤ p → p ≤ 1 → demandOut x p = (1 - x) * (1 - p)) := by sorry

end GDPRPrivacy.PriceRise

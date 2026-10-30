-- Prove2me | Theorems.Thm_MarketplaceSharing_Threshold_corollary_1
-- name    : MarketplaceSharing.Threshold.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:41.452495+00:00
-- url     : https://prove2.me/theorems/4fe342a5-c030-4f81-8ccc-469d9d29aac2
-- title:
--   Corollary 1, p. 10 — the sharing thresholds are nondecreasing in the number of units, tₙ₊₁ ≥ tₙ
-- statement:
--   Let $(V_n)_{n\ge0}$ be the revenue-to-go of the inventory sharing model (a solution of the HJB system (3) with $V_0 \equiv 0$ and $V_n(0) = 0$), and let $t_n = \sup\{t \ge 0 : \Delta V_n(t) \le (1-\theta)\pi\} \in [0,\infty]$ be the sharing threshold of unit $n$. Then for every $n \ge 1$,
--   $$t_{n+1} \ge t_n.$$
--
--   The more units are left, the earlier in the season (the larger the time-to-go) the supplier starts sharing. This is what makes the intervals $[t_{j-1}, t_j]$ of Theorem 1 tile $[0,\infty)$.
--
--   **Formalization Note.** The inequality is in the extended reals, so it includes the case $t_n = \infty$ (then $t_{n+1} = \infty$). $n$ ranges over $n \ge 1$.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), p. 10, Corollary 1

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

namespace MarketplaceSharing.Threshold
theorem corollary_1 (p : Params) (V : ℕ → ℝ → ℝ) (hV : p.IsRevenueToGo V) :
    ∀ n : ℕ, 1 ≤ n → p.threshold V n ≤ p.threshold V (n + 1) := by sorry
end MarketplaceSharing.Threshold

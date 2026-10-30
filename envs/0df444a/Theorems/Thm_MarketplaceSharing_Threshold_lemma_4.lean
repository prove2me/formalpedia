-- Prove2me | Theorems.Thm_MarketplaceSharing_Threshold_lemma_4
-- name    : MarketplaceSharing.Threshold.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:20.175461+00:00
-- url     : https://prove2.me/theorems/08aad8a5-52e0-4756-88d1-b1253ed969ca
-- title:
--   Lemma 4, p. 9 — ΔVₙ(t) is nondecreasing in time-to-go (the printed display has the inequality reversed; the statement follows its words and proof)
-- statement:
--   Let $(V_n)_{n\ge0}$ be the revenue-to-go of the inventory sharing model (a solution of the HJB system (3) with $V_0 \equiv 0$ and $V_n(0) = 0$), and $\Delta V_n(t) = V_n(t) - V_{n-1}(t)$. Then for every $n \ge 1$ and all times-to-go $t_2 \ge t_1 > 0$,
--   $$\Delta V_n(t_1) \le \Delta V_n(t_2).$$
--
--   The marginal unit is worth more when more time is left to sell it. This is what makes the set of times at which sharing pays an interval $[0, t_n]$.
--
--   **Formalization Note.** The lemma's words ("the marginal revenue-to-go is increasing with the time left") and its proof (p. 30: "$\Delta V_n(t+1) - \Delta V_n(t) \ge 0$") give this direction; the printed display $\Delta V_n(t_2) \le \Delta V_n(t_1)$ has the inequality reversed and is false, since $\Delta V_n(0) = 0$ and $\Delta V_n(t) > 0$ for $t > 0$. The printed $t_1 > 0$ is kept; $n \in \{1,\dots,N\}$ is read as $n \ge 1$.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), p. 9, Lemma 4 (direction as in its words and in its proof, Appendix pp. 29–30)

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

namespace MarketplaceSharing.Threshold
theorem lemma_4 (p : Params) (V : ℕ → ℝ → ℝ) (hV : p.IsRevenueToGo V) :
    ∀ n : ℕ, 1 ≤ n → ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ t₂ → marginal V n t₁ ≤ marginal V n t₂ := by sorry
end MarketplaceSharing.Threshold

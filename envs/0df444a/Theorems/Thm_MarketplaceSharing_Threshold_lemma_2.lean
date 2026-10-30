-- Prove2me | Theorems.Thm_MarketplaceSharing_Threshold_lemma_2
-- name    : MarketplaceSharing.Threshold.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:20.957729+00:00
-- url     : https://prove2.me/theorems/7b858780-df84-4957-a907-bfc7f5e3b8d3
-- title:
--   Lemma 2, p. 9 — the marginal revenue-to-go ΔVₙ(t) is decreasing in the number of units
-- statement:
--   Let $(V_n)_{n\ge0}$ be the revenue-to-go of the inventory sharing model (a solution of the HJB system (3) with $V_0 \equiv 0$ and $V_n(0) = 0$), and $\Delta V_n(t) = V_n(t) - V_{n-1}(t)$. Then for every $n \ge 1$ and every time-to-go $t \ge 0$,
--   $$\Delta V_n(t) \ge \Delta V_{n+1}(t).$$
--
--   The revenue-to-go is concave in the number of units: each additional unit is worth at most as much as the previous one.
--
--   **Formalization Note.** $n \in \{1,\dots,N\}$ is read as $n \ge 1$. "Decreasing" is the weak inequality printed in the lemma. $V$ is any solution of (3), carried as a hypothesis.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), p. 9, Lemma 2

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

namespace MarketplaceSharing.Threshold
theorem lemma_2 (p : Params) (V : ℕ → ℝ → ℝ) (hV : p.IsRevenueToGo V) :
    ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → marginal V (n + 1) t ≤ marginal V n t := by sorry
end MarketplaceSharing.Threshold

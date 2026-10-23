-- Prove2me | Theorems.Thm_MarketplaceSharing_Threshold_lemma_3
-- name    : MarketplaceSharing.Threshold.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:28.601042+00:00
-- url     : https://prove2.me/theorems/e9024b27-8e6e-4703-8a8a-223c07cb9cd0
-- title:
--   Lemma 3, p. 9 — the revenue-to-go Vₙ(t) is increasing in the time-to-go
-- statement:
--   Let $(V_n)_{n\ge0}$ be the revenue-to-go of the inventory sharing model (a solution of the HJB system (3) with $V_0 \equiv 0$ and $V_n(0) = 0$). Then for every $n \ge 1$ and all times-to-go $t_2 \ge t_1 > 0$,
--   $$V_n(t_2) \ge V_n(t_1).$$
--
--   More time left in the season never lowers the expected revenue from a given stock.
--
--   **Formalization Note.** The printed restriction $t_1 > 0$ is kept. $n \in \{1,\dots,N\}$ is read as $n \ge 1$. $V$ is any solution of (3), carried as a hypothesis.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), p. 9, Lemma 3

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

namespace MarketplaceSharing.Threshold
theorem lemma_3 (p : Params) (V : ℕ → ℝ → ℝ) (hV : p.IsRevenueToGo V) :
    ∀ n : ℕ, 1 ≤ n → ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ t₂ → V n t₁ ≤ V n t₂ := by sorry
end MarketplaceSharing.Threshold

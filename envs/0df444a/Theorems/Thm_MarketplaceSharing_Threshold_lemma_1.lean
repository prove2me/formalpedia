-- Prove2me | Theorems.Thm_MarketplaceSharing_Threshold_lemma_1
-- name    : MarketplaceSharing.Threshold.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:26.364117+00:00
-- url     : https://prove2.me/theorems/e4d03477-2576-4fc4-bc56-8dc88c3719b8
-- title:
--   Lemma 1, p. 8 — the revenue-to-go Vₙ(t) is increasing in the number of units
-- statement:
--   Let $(V_n)_{n\ge0}$ be the revenue-to-go of the inventory sharing model, i.e. a solution of the HJB system (3) with $V_0 \equiv 0$ and $V_n(0) = 0$. Then for every $n \ge 1$ and every time-to-go $t \ge 0$,
--   $$V_{n+1}(t) \ge V_n(t).$$
--
--   One more unit in stock never lowers the supplier's expected discounted revenue.
--
--   **Formalization Note.** The paper's range $n \in \{1,\dots,N\}$ is read as $n \ge 1$, since $V_n$ does not depend on the initial stock $N$. $V$ is any solution of (3), carried as a hypothesis.
-- source:
--   Martínez-de-Albéniz, Pinto & Amorim, Driving Supply to Marketplaces, SSRN 3643261 (June 30, 2020), p. 8, Lemma 1

import Mathlib
import Definitions.Def_MarketplaceSharing_Threshold_Model

namespace MarketplaceSharing.Threshold
theorem lemma_1 (p : Params) (V : ℕ → ℝ → ℝ) (hV : p.IsRevenueToGo V) :
    ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → V n t ≤ V (n + 1) t := by sorry
end MarketplaceSharing.Threshold

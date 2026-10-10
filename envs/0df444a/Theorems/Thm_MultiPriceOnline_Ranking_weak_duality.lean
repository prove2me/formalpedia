-- Prove2me | Theorems.Thm_MultiPriceOnline_Ranking_weak_duality
-- name    : MultiPriceOnline.Ranking.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:22.70049+00:00
-- url     : https://prove2.me/theorems/eeacaf45-2858-46e1-ad3a-72ec75e38cdf
-- title:
--   (19), p. 19 — weak duality: every feasible solution of (5) is bounded by every feasible dual solution of (19)
-- statement:
--   Fix a setup — $n$ items with inventories $k_i$ and prices $r_i^{(1)},\dots,r_i^{(m_i)}$ — and an arrival sequence of $T$ customers with purchase probabilities $p^{(j)}_{t,i}\in[0,1]$. Let $x$ be feasible for the LP (5) and $(y,z)$ feasible for its dual (19). Then
--   $$\sum_{t=1}^T\sum_{i=1}^n\sum_{j=1}^{m_i}p^{(j)}_{t,i}\,r_i^{(j)}\,x^{(j)}_{t,i}\ \le\ \sum_{i=1}^n k_iy_i+\sum_{t=1}^T z_t .$$
--
--   In particular $\mathrm{OPT}(\mathcal S,\mathcal A)$ is at most the objective value of any feasible dual solution; the proof of Theorem 2 combines this with Lemma 3.
--
--   **Formalization Note** The standing assumption $0\le p^{(j)}_{t,i}\le1$ is a hypothesis. The same statement is a milestone of the companion mission on Multi-price Balance; it is restated here because draft items cannot import another mission's drafts.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 19, (19a)–(19c) and the sentence after (19c)

import Mathlib
import Definitions.Def_MultiPriceOnline_Ranking_LP

namespace MultiPriceOnline.Ranking

/-- Weak duality for the LP (5) and its dual (19) (p. 19): the objective of every feasible
solution of (5) is at most the objective of every feasible solution of (19). The purchase
probabilities satisfy the standing assumption `0 ≤ p ≤ 1`. -/
theorem weak_duality {n T : ℕ} (k m : Fin n → ℕ) (r : Fin n → ℕ → ℝ)
    (p : Fin T → Fin n → ℕ → ℝ)
    (hp : ∀ t i j, 1 ≤ j → j ≤ m i → 0 ≤ p t i j ∧ p t i j ≤ 1)
    (x : Fin T → Fin n → ℕ → ℝ) (hx : LPFeasible k m p x)
    (y : Fin n → ℝ) (z : Fin T → ℝ) (hyz : DualFeasible m r p y z) :
    lpObj m r p x ≤ dualObj k y z := by sorry

end MultiPriceOnline.Ranking

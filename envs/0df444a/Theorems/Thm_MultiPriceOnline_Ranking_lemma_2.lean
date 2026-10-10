-- Prove2me | Theorems.Thm_MultiPriceOnline_Ranking_lemma_2
-- name    : MultiPriceOnline.Ranking.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:42.566646+00:00
-- url     : https://prove2.me/theorems/218b1e8a-35f8-4273-a7e1-b5ff2a5d3e6f
-- title:
--   Lemma 2, p. 22 — if Algorithm 2 assigns item i to customer t, then (1 − e^{−αᵢ⁽¹⁾})(Yᵢ + Zₜ) ≤ rᵢ^{(jₜ,ᵢ)}
-- statement:
--   Consider Multi-price Ranking (Algorithm 2) in the deterministic case: item $i$ has price set $\mathcal P_i=\{r_i^{(1)}<\dots<r_i^{(m_i)}\}$ with booking limits $\alpha_i^{(1)},\dots,\alpha_i^{(m_i)}$ (Proposition 1), every $p^{(j)}_{t,i}\in\{0,1\}$, seeds $W\in[0,1]^n$, and an arbitrary tie-breaking rule that returns a maximizer of (23). Let $Y_i$ and $Z_t$ be the dual variables set by the run. If the run assigns item $i$ to customer $t$, then
--   $$\bigl(1-e^{-\alpha_i^{(1)}}\bigr)\,(Y_i+Z_t)\ \le\ r_i^{(j_{t,i})}.$$
--
--   Summed over the assigned pairs, this bounds $\sum_iY_i+\sum_tZ_t$ by the revenue divided by $\min_i F(\mathcal P_i)$, which is one half of the proof of Theorem 2.
--
--   **Formalization Note** The paper states the inequality "w.p.1" because $Y_i=\Phi'_{\mathcal P_i}(W_i)$ is undefined at the segment borders. Here $\Phi'$ is the explicit derivative of (9) on the segment $\ell(W_i)$ (the right derivative at a border), and the inequality is claimed for every seed vector in $[0,1]^n$, which implies the almost-sure statement.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 22, Lemma 2 (proof: App. C, p. 45)

import Mathlib
import Definitions.Def_MultiPriceOnline_Ranking_LP
import Definitions.Def_MultiPriceOnline_Ranking_Setting

namespace MultiPriceOnline.Ranking

/-- Lemma 2 (p. 22): if Algorithm 2 assigns item `i` to customer `t`, then
`(1 - e^{-α_i^{(1)}}) (Y_i + Z_t) ≤ r_i^{(j_{t,i})}`. Stated for every seed vector in `[0, 1]ⁿ`
(not only almost surely), with `Y_i` the explicit (right) derivative `PhiDeriv`. -/
theorem lemma_2 {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, IsPriceSet (m i) (r i)) (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (hp : IsDeterministic m p)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (W : Fin n → ℝ) (hW : ∀ i, W i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) (t : Fin T) (hti : run2 m r α p sel Finset.univ W t = some i) :
    (1 - Real.exp (-α i 1)) *
        (Yi m r α p sel Finset.univ W i + Zt m r α p sel Finset.univ W t) ≤
      MultiPriceOnline.Balance.pr (r i) (jt m (p t) i) := by sorry

end MultiPriceOnline.Ranking

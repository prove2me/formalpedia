-- Prove2me | Theorems.Thm_MultiPriceOnline_Balance_proposition_3
-- name    : MultiPriceOnline.Balance.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:55.37073+00:00
-- url     : https://prove2.me/theorems/598efea0-6e2f-477d-9588-b79108eb7231
-- title:
--   Proposition 3, p. 21 — Definition 3's comonotone rounding: E[L̃⁽ʲ⁾] = L⁽ʲ⁾ and |(L̃⁽ʲ⁾ − L̃⁽ʲ′⁾) − (L⁽ʲ⁾ − L⁽ʲ′⁾)| ≤ 1/k
-- statement:
--   Let $k\ge1$ be an integer and let $0<r^{(1)}<\dots<r^{(m)}$ be a price set with $m\ge1$. Let $\alpha$ be its booking limits (7), with borders $L^{(j)}=\alpha^{(1)}+\dots+\alpha^{(j)}$. Draw $W$ uniformly from $[0,1]$ and round every $L^{(j)}k$ with the same seed (Definition 3): up if $W<L^{(j)}k-\lfloor L^{(j)}k\rfloor$, down otherwise. Write $\tilde L^{(j)}$ for the result divided by $k$. Then
--   $$
--   \mathbb E\big[\tilde L^{(j)}\big]=L^{(j)},\qquad j=0,\dots,m,\tag{21}
--   $$
--   and for every seed $W\in[0,1]$
--   $$
--   \Big|\big(\tilde L^{(j)}-\tilde L^{(j')}\big)-\big(L^{(j)}-L^{(j')}\big)\Big|\le\frac1k,\qquad 1\le j'<j\le m.\tag{22}
--   $$
--
--   Each border may move by up to $1/k$, but because all borders are rounded with one seed, the length of any union of consecutive segments moves by at most $1/k$. This is the property the proof of Theorem 5 relies on.
--
--   **Formalization Note** The expectation in (21) is the integral over $W\in[0,1]$ of $\tilde L^{(j)}$ as a function of the seed, not an expectation under the induced distribution on configurations. (22) is stated for every seed in $[0,1]$, which is what the paper's proof shows.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 21, Proposition 3, (21)–(22); proof in App. B.1, pp. 40–41

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_Procedure

namespace MultiPriceOnline.Balance

/-- Proposition 3 (Ma–Simchi-Levi, arXiv:1905.04770v1, p. 21). For an item with inventory `k ≥ 1`
and booking limits `α` of a price set with `m ≥ 1` prices, the random borders `L̃⁽ʲ⁾` of
Definition 3 (seed `W` uniform on `[0, 1]`) satisfy
(21) `𝔼[L̃⁽ʲ⁾] = L⁽ʲ⁾` for `j = 0, …, m`, and
(22) `|(L̃⁽ʲ⁾ − L̃⁽ʲ'⁾) − (L⁽ʲ⁾ − L⁽ʲ'⁾)| ≤ 1/k` for `1 ≤ j' < j ≤ m`, for every seed `W ∈ [0, 1]`.
In unit indices `L̃⁽ʲ⁾ = cv (def3Config k m α W) j / k`. -/
theorem proposition_3 (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (r α : ℕ → ℝ)
    (hr : IsPriceSet m r) (hα : IsBookingLimits m r α) :
    (∀ j, j ≤ m →
      ∫ W in (0 : ℝ)..1, (cv (def3Config k m α W) j : ℝ) / k = Lsum α j) ∧
    (∀ W ∈ Set.Icc (0 : ℝ) 1, ∀ j j' : ℕ, 1 ≤ j' → j' < j → j ≤ m →
      |((cv (def3Config k m α W) j : ℝ) / k - (cv (def3Config k m α W) j' : ℝ) / k) -
          (Lsum α j - Lsum α j')| ≤ 1 / k) := by sorry

end MultiPriceOnline.Balance

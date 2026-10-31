-- Prove2me | Theorems.Thm_NontruthfulPA_theorem_1
-- name    : NontruthfulPA.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:27.349876+00:00
-- url     : https://prove2.me/theorems/85e2e8c5-64b8-4703-91f8-e0d70a455fbd
-- title:
--   Theorem 1 — the $\alpha$-GSP mechanism has an efficient equilibrium whenever the $\alpha$-VCG mechanism does (corrected: position-deviation equilibrium)
-- statement:
--   Let $k \le n$, let $\alpha, \beta \in \mathbb R^k_\ge$ be positive and non-increasing (with $\alpha_j = \beta_j = 0$ for $j > k$), and let $v \in \mathbb R^n$ with $v_i \ge 0$; bidder $i$ values position $j$ at $\beta_j v_i$, while the mechanisms read a bid $b_i$ as the vector $(\alpha_j b_i)_j$. Then
--
--   $$\text{the } \alpha\text{-VCG mechanism possesses an efficient equilibrium} \ \Longrightarrow\ \text{the } \alpha\text{-GSP mechanism possesses an efficient equilibrium.}$$
--
--   Here an equilibrium is a non-negative bid profile $b$ with an allocation $\sigma$ (positions in non-increasing order of bids, ties resolved by $\sigma$) such that no bidder gains by being moved to any other position, the other bidders keeping their order, at the price the mechanism charges there; it is efficient if $\sigma$ assigns positions in order of the values $v$. The $\alpha$-VCG mechanism charges the position-$g$ bidder $\sum_{j=g}^{k} (\alpha_j - \alpha_{j+1}) b_{(j+1)}$, the $\alpha$-GSP mechanism $\alpha_g b_{(g+1)}$.
--
--   The theorem says that the non-truthful generalized second price auction is at least as robust as the VCG-style auction to a misspecified estimate $\alpha$ of the relative position values $\beta$. Values need not be sorted and the rankings are existential.
--
--   **Formalization Note** Bidders are `Fin n`, positions are 0-based ranks, rankings are `Equiv.Perm (Fin n)`, and $\alpha, \beta$ are functions on $\mathbb N$ vanishing from index $k$ on. The equilibrium is the position-deviation equilibrium in both the hypothesis and the conclusion.
--
--   Differences from the source:
--   - correction: Nash equilibrium of p.6 (every real deviation x under a fixed tie-breaking allocation; efficient: b_i > b_j whenever v_i > v_j) → position-deviation equilibrium with a ranking σ that orders the bids (ties resolved by σ) and, for efficiency, also the values, in both hypothesis and conclusion; reason: the printed theorem is false under the p.6 notion: k = 2, n = 3, α = (0.6, 0.3), β = (0.7, 0.4), v = (8, 7, 6); b = (9, 8, 0) is an efficient α-VCG Nash equilibrium, while an efficient α-GSP one needs b_1 > b_2 > b_3 ≥ 0 with 0.3 b_2 ≥ 2.4 (bidder 3 must not take position 2) and 0.6 b_2 − 0.3 b_3 ≤ 2.4 (bidder 1 must not drop to position 2), which force b_2 ≥ 8 and b_2 < 8. The paper's proof works with the position deviations of p.8 and p.11
--   - reading: bid profiles b ∈ ℝ^n (p.6) → bids b_i ≥ 0; reason: mechanisms charge non-negative payments (p.6) and §3.1 uses b_3 ≥ 0 (p.8); with negative bids the payments could be negative
--   - reading: v ∈ ℝ^n with β_j v_i ≥ 0 the value for position j (p.6) → v_i ≥ 0; reason: β_j > 0 for j ≤ k, so β_j v_i ≥ 0 is v_i ≥ 0
--   - encoding: bidders and positions 1,…,n; α, β ∈ ℝ^k with α_j = β_j = 0 for j > k; b_(i) = 0 for i > n → Fin n with 0-based ranks; α, β : ℕ → ℝ positive and non-increasing below k and 0 from k on; rank lists ℕ → ℝ padded by 0; reason: Lean convention; same instances
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, Theorem 1, p.11 (proof pp.11–14)

import Mathlib
import Definitions.Def_NontruthfulPA_Model

namespace NontruthfulPA

/-- **Theorem 1** (corrected: position-deviation equilibrium), Dütting–Fischer–Parkes,
*Non-Truthful Position Auctions Are More Robust to Misspecification*, arXiv:1602.07593v4, p.11:
"Let α, β ∈ ℝ^k_≥, v ∈ ℝ^n. Then the α-GSP mechanism possesses an efficient Nash equilibrium
for valuations given by β and v whenever the α-VCG mechanism does."

For every `k ≤ n`, every `α, β ∈ ℝ^k_≥` (positive, non-increasing on the `k` positions, zero
beyond) and every non-negative value vector `v`: if some bid profile with some ranking is an
efficient α-VCG equilibrium, then some bid profile with some ranking is an efficient α-GSP
equilibrium.

**Formalization Note.** Bidders `Fin n`, positions 0-based ranks `Fin n`; rankings are
`Equiv.Perm (Fin n)` and resolve ties in the bids. Equilibrium is the position-deviation
equilibrium `IsPDEquilibrium` in both hypothesis and conclusion: this is the declared
correction, since under the literal p.6 definition (real-valued deviations under a fixed
tie-breaking, efficiency `b_i > b_j` whenever `v_i > v_j`) the statement fails for `k = 2`,
`n = 3`, `α = (0.6, 0.3)`, `β = (0.7, 0.4)`, `v = (8, 7, 6)`. Bids are non-negative, and
`v ≥ 0` is the p.6 requirement `β_j v_i ≥ 0`. -/
theorem theorem_1 {k n : ℕ} (hkn : k ≤ n) {α β : ℕ → ℝ} (hα : IsPosVec k α)
    (hβ : IsPosVec k β) (v : Fin n → ℝ) (hv0 : ∀ i, 0 ≤ v i)
    (h : HasEfficientEquilibrium (payV k α) β v) :
    HasEfficientEquilibrium (payS α) β v := by sorry

end NontruthfulPA

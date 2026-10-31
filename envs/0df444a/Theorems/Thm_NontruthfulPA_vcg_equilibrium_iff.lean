-- Prove2me | Theorems.Thm_NontruthfulPA_vcg_equilibrium_iff
-- name    : NontruthfulPA.vcg_equilibrium_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:19.764515+00:00
-- url     : https://prove2.me/theorems/804ecea5-a5f8-41bd-8045-8eeb52f16e07
-- title:
--   (23)–(24) — the $\alpha$-VCG equilibrium conditions for sorted profiles
-- statement:
--   There are $k$ positions and $n \ge k$ bidders. The position vectors $\alpha, \beta \in \mathbb R^k_\ge$ are positive and non-increasing, with $\alpha_j = \beta_j = 0$ for $j > k$; bidder $i$ values position $j$ at $\beta_j v_i$ with $v_i \ge 0$. Bids are $b \in [0,\infty)^n$, and $b_{(t)}$ denotes the $t$-th highest bid, with $b_{(t)} = 0$ for $t > n$.
--
--   Assume $v_1 \ge \dots \ge v_n$ and let $b$ be a bid profile with $b_1 \ge \dots \ge b_n \ge 0$, bidder $i$ in position $i$; write $b_t = 0$ for $t > n$. Then $b$ is an equilibrium of the $\alpha$-VCG mechanism if and only if for all $i, j \in \{1, \dots, n\}$,
--   $$(\alpha_j - \alpha_{j+1})\, b_j \ \ge\ (\beta_j - \beta_i)\, v_i - \sum_{t=j+1}^{i-1} (\alpha_t - \alpha_{t+1})\, b_t \qquad \text{if } j < i, \tag{23}$$
--   $$(\alpha_i - \alpha_{i+1})\, b_{i+1} \ \le\ (\beta_i - \beta_j)\, v_i - \sum_{t=i+1}^{j-1} (\alpha_t - \alpha_{t+1})\, b_{t+1} \qquad \text{if } j > i. \tag{24}$$
--
--   Condition (23) says that bidder $i$ does not gain by moving up to position $j$, where the bidders it passes move down one position and its payment may rise; (24) says that it does not gain by moving down to position $j$, at that position's current payment.
--
--   **Formalization Note** Bidders are `Fin n` and positions are 0-based ranks (rank $r$ is position $r+1$); $\alpha, \beta$ are functions on $\mathbb N$ that vanish from index $k$ on; the bids in rank order are padded by $0$ past rank $n$. Equilibrium is the position-deviation equilibrium of the mission's model.
--
--   Differences from the source:
--   - generalization: a sorted profile is an α-VCG equilibrium if (23) and (24) hold → if and only if; reason: each condition is exactly one position deviation, so the converse holds too; the equivalence contains the page's implication
--   - reading: (Nash) equilibrium: p.6 allows every real deviation x under a fixed tie-breaking allocation; §3.1 (p.8) and §3.2 (p.11) describe it as a bidder raising or lowering its bid and being assigned a different position → IsPDEquilibrium: for every bidder i and every position r, moving i to r (others keep their order) at the price the mechanism charges on the deviated rank list does not raise i's utility; ties are resolved by the ranking σ; reason: §3's own notion; the mission uses it throughout because the main theorem is false under the p.6 notion (see Theorem 1)
--   - reading: bid profiles b ∈ ℝ^n (p.6) → bids b_i ≥ 0; reason: mechanisms charge non-negative payments (p.6) and §3.1 uses b_3 ≥ 0 (p.8); with negative bids the payments could be negative
--   - reading: v ∈ ℝ^n with β_j v_i ≥ 0 the value for position j (p.6) → v_i ≥ 0; reason: β_j > 0 for j ≤ k, so β_j v_i ≥ 0 is v_i ≥ 0
--   - encoding: WLOG v_1 ≥ ⋯ ≥ v_n and bidder i is assigned position i (p.11) → v and b antitone on Fin n and the identity ranking Equiv.refl; reason: the paper's sorted frame, written out
--   - encoding: bidders and positions 1,…,n; α, β ∈ ℝ^k with α_j = β_j = 0 for j > k; b_(i) = 0 for i > n → Fin n with 0-based ranks; α, β : ℕ → ℝ positive and non-increasing below k and 0 from k on; rank lists ℕ → ℝ padded by 0; reason: Lean convention; same instances
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, §3.2, (23)–(24), p.11

import Mathlib
import Definitions.Def_NontruthfulPA_Model

namespace NontruthfulPA

/-- **α-VCG equilibrium conditions (23)–(24)**, Dütting–Fischer–Parkes, *Non-Truthful Position
Auctions Are More Robust to Misspecification*, arXiv:1602.07593v4, §3.2, p.11: "a bid profile
b with b1 ≥ ⋯ ≥ bn is a Nash equilibrium of the α-VCG mechanism if for all i, j ∈ {1,…,n},
(α_j − α_{j+1}) b_j ≥ (β_j − β_i) v_i − Σ_{t=j+1}^{i−1} (α_t − α_{t+1}) b_t if j < i, (23)
(α_i − α_{i+1}) b_{i+1} ≤ (β_i − β_j) v_i − Σ_{t=i+1}^{j−1} (α_t − α_{t+1}) b_{t+1} if j > i. (24)"

Stated as an equivalence, in the sorted frame of p.11 (bidder `i` holds rank `i`, identity
ranking).

**Formalization Note.** 0-based indices: bidder/rank `i : Fin n` is the paper's `i + 1`; the
formulas keep their shape under the shift. `padBids b t` is `b_{t+1}` for `t < n` and `0` for
`t ≥ n` (the convention `b_(i) = 0` for `i > n`, p.7). Equilibrium is the position-deviation
equilibrium `IsPDEquilibrium` (declared correction of p.6). The page states "if"; under the
position-deviation equilibrium the derivation is exact, so the equivalence is posed. -/
theorem vcg_equilibrium_iff {k n : ℕ} (hkn : k ≤ n) {α β : ℕ → ℝ} (hα : IsPosVec k α)
    (hβ : IsPosVec k β) {v b : Fin n → ℝ} (hv0 : ∀ i, 0 ≤ v i) (hv : Antitone v)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Antitone b) :
    IsPDEquilibrium (payV k α) β v b (Equiv.refl (Fin n)) ↔
      ((∀ i j : Fin n, j < i →
          (β j - β i) * v i - ∑ t ∈ Finset.Ico ((j : ℕ) + 1) i, (α t - α (t + 1)) * padBids b t
            ≤ (α j - α (j + 1)) * padBids b j) ∧
        (∀ i j : Fin n, i < j →
          (α i - α (i + 1)) * padBids b (i + 1) ≤
            (β i - β j) * v i -
              ∑ t ∈ Finset.Ico ((i : ℕ) + 1) j, (α t - α (t + 1)) * padBids b (t + 1))) := by sorry

end NontruthfulPA

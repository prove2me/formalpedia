-- Prove2me | Theorems.Thm_NontruthfulPA_local_downward_imp_24
-- name    : NontruthfulPA.local_downward_imp_24
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:19.374901+00:00
-- url     : https://prove2.me/theorems/33288e9a-ee08-44fd-aa15-2a2e7874019b
-- title:
--   p.12 — the case $j = i+1$ of (24) implies all cases
-- statement:
--   There are $k$ positions and $n \ge k$ bidders. The position vectors $\alpha, \beta \in \mathbb R^k_\ge$ are positive and non-increasing, with $\alpha_j = \beta_j = 0$ for $j > k$; bidder $i$ values position $j$ at $\beta_j v_i$ with $v_i \ge 0$. Bids are $b \in [0,\infty)^n$, and $b_{(t)}$ denotes the $t$-th highest bid, with $b_{(t)} = 0$ for $t > n$.
--
--   Assume $v_1 \ge \dots \ge v_n$ and $b_1 \ge \dots \ge b_n \ge 0$, bidder $i$ in position $i$, $b_t = 0$ for $t > n$. If
--   $$(\alpha_t - \alpha_{t+1})\, b_{t+1} \le (\beta_t - \beta_{t+1})\, v_t \qquad \text{for all } t \in \{1, \dots, n-1\},$$
--   then (24) holds for all $i < j$:
--   $$(\alpha_i - \alpha_{i+1})\, b_{i+1} \ \le\ (\beta_i - \beta_j)\, v_i - \sum_{t=i+1}^{j-1} (\alpha_t - \alpha_{t+1})\, b_{t+1}.$$
--
--   So for an efficient $\alpha$-VCG equilibrium only the move down by one position constrains the bids from above.
--
--   **Formalization Note** Bidders are `Fin n` and positions are 0-based ranks (rank $r$ is position $r+1$); $\alpha, \beta$ are functions on $\mathbb N$ that vanish from index $k$ on; the bids in rank order are padded by $0$ past rank $n$.
--
--   Differences from the source:
--   - generalization: b an efficient α-VCG equilibrium → b sorted and non-negative satisfying the case j = i + 1 of (24); reason: the page's argument uses only that case and efficiency; every efficient α-VCG equilibrium satisfies it by (24)
--   - reading: bid profiles b ∈ ℝ^n (p.6) → bids b_i ≥ 0; reason: mechanisms charge non-negative payments (p.6) and §3.1 uses b_3 ≥ 0 (p.8); with negative bids the payments could be negative
--   - reading: v ∈ ℝ^n with β_j v_i ≥ 0 the value for position j (p.6) → v_i ≥ 0; reason: β_j > 0 for j ≤ k, so β_j v_i ≥ 0 is v_i ≥ 0
--   - encoding: WLOG v_1 ≥ ⋯ ≥ v_n and bidder i is assigned position i (p.11) → v and b antitone on Fin n and the identity ranking Equiv.refl; reason: the paper's sorted frame, written out
--   - encoding: bidders and positions 1,…,n; α, β ∈ ℝ^k with α_j = β_j = 0 for j > k; b_(i) = 0 for i > n → Fin n with 0-based ranks; α, β : ℕ → ℝ positive and non-increasing below k and 0 from k on; rank lists ℕ → ℝ padded by 0; reason: Lean convention; same instances
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, proof of Lemma 1, p.12, "For (24), the case where j = i + 1 implies all other cases"

import Mathlib
import Definitions.Def_NontruthfulPA_Model

namespace NontruthfulPA

/-- **The case `j = i + 1` of (24) implies all cases**, Dütting–Fischer–Parkes, *Non-Truthful
Position Auctions Are More Robust to Misspecification*, arXiv:1602.07593v4, proof of Lemma 1,
p.12: "For (24), the case where j = i + 1 implies all other cases, because
(β_i − β_j) v_i − Σ_{t=i+1}^{j−1} (α_t − α_{t+1}) b_{t+1}
≥ (β_i − β_j) v_i − Σ_{t=i+1}^{j−1} (β_t − β_{t+1}) v_t
≥ (β_i − β_j) v_i − Σ_{t=i+1}^{j−1} (β_t − β_{t+1}) v_i = (β_i − β_{i+1}) v_i".

In the sorted frame of p.11 (`v` and `b` non-increasing, bidder `i` at rank `i`): if
`(α_t − α_{t+1}) b_{t+1} ≤ (β_t − β_{t+1}) v_t` for every `t ∈ {1, …, n−1}`, then (24) holds
for all `i < j`.

**Formalization Note.** 0-based indices (`t` here is the paper's `t + 1`); `padBids b t` is
`b_{t+1}`, `0` past the end. The page uses this inside the proof for an efficient equilibrium
`b`; the statement assumes only the local inequality, which every efficient α-VCG equilibrium
satisfies by (24). -/
theorem local_downward_imp_24 {k n : ℕ} (hkn : k ≤ n) {α β : ℕ → ℝ} (hα : IsPosVec k α)
    (hβ : IsPosVec k β) {v b : Fin n → ℝ} (hv0 : ∀ i, 0 ≤ v i) (hv : Antitone v)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Antitone b)
    (hloc : ∀ (t : ℕ) (h : t + 1 < n),
      (α t - α (t + 1)) * padBids b (t + 1) ≤ (β t - β (t + 1)) * v ⟨t, Nat.lt_of_succ_lt h⟩) :
    ∀ i j : Fin n, i < j →
      (α i - α (i + 1)) * padBids b (i + 1) ≤
        (β i - β j) * v i -
          ∑ t ∈ Finset.Ico ((i : ℕ) + 1) j, (α t - α (t + 1)) * padBids b (t + 1) := by sorry

end NontruthfulPA

-- Prove2me | Theorems.Thm_NontruthfulPA_local_envy_free_imp_25
-- name    : NontruthfulPA.local_envy_free_imp_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:22.84373+00:00
-- url     : https://prove2.me/theorems/16a75436-9252-46e6-9b7a-98326438aa34
-- title:
--   p.13 — local envy-freeness (27) implies (25)
-- statement:
--   There are $k$ positions and $n \ge k$ bidders. The position vectors $\alpha, \beta \in \mathbb R^k_\ge$ are positive and non-increasing, with $\alpha_j = \beta_j = 0$ for $j > k$; bidder $i$ values position $j$ at $\beta_j v_i$ with $v_i \ge 0$. Bids are $b \in [0,\infty)^n$, and $b_{(t)}$ denotes the $t$-th highest bid, with $b_{(t)} = 0$ for $t > n$.
--
--   Assume $v_1 \ge \dots \ge v_n$ and $b_1 \ge \dots \ge b_n \ge 0$, bidder $i$ in position $i$, $b_t = 0$ for $t > n$. If (27) holds, i.e.
--   $$(\alpha_{i-1} - \alpha_i)\, b_i \ge (\beta_{i-1} - \beta_i)\, v_i \qquad \text{for all } i \in \{2, \dots, n\},$$
--   then (25) holds for all $j < i$:
--   $$(\alpha_j - \alpha_{j+1})\, b_{j+1} \ \ge\ (\beta_j - \beta_i)\, v_i - \sum_{t=j+1}^{i-1} (\alpha_t - \alpha_{t+1})\, b_{t+1}.$$
--
--   Subject to efficiency, local envy-freeness with regard to the position directly above implies envy-freeness with regard to all higher positions (footnote 10).
--
--   **Formalization Note** Bidders are `Fin n` and positions are 0-based ranks (rank $r$ is position $r+1$); $\alpha, \beta$ are functions on $\mathbb N$ that vanish from index $k$ on; the bids in rank order are padded by $0$ past rank $n$.
--
--   Differences from the source:
--   - generalization: b the bidder-pessimal profile (26), which satisfies (27) → any sorted non-negative b satisfying (27); reason: the page's argument uses only (27) and the ordering of v; the pessimal profile is an instance
--   - reading: bid profiles b ∈ ℝ^n (p.6) → bids b_i ≥ 0; reason: mechanisms charge non-negative payments (p.6) and §3.1 uses b_3 ≥ 0 (p.8); with negative bids the payments could be negative
--   - reading: v ∈ ℝ^n with β_j v_i ≥ 0 the value for position j (p.6) → v_i ≥ 0; reason: β_j > 0 for j ≤ k, so β_j v_i ≥ 0 is v_i ≥ 0
--   - encoding: WLOG v_1 ≥ ⋯ ≥ v_n and bidder i is assigned position i (p.11) → v and b antitone on Fin n and the identity ranking Equiv.refl; reason: the paper's sorted frame, written out
--   - encoding: bidders and positions 1,…,n; α, β ∈ ℝ^k with α_j = β_j = 0 for j > k; b_(i) = 0 for i > n → Fin n with 0-based ranks; α, β : ℕ → ℝ positive and non-increasing below k and 0 from k on; rank lists ℕ → ℝ padded by 0; reason: Lean convention; same instances
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, proof of Lemma 1, p.13, "For the general case let i, j ∈ {1, . . . , n} with j < i", and footnote 10

import Mathlib
import Definitions.Def_NontruthfulPA_Model

namespace NontruthfulPA

/-- **(27) implies (25)**, Dütting–Fischer–Parkes, *Non-Truthful Position Auctions Are More
Robust to Misspecification*, arXiv:1602.07593v4, proof of Lemma 1, p.13: "For the general case
let i, j ∈ {1,…,n} with j < i. Then
(β_j − β_i) v_i − Σ_{t=j+1}^{i−1} (α_t − α_{t+1}) b_{t+1} ≤ (β_j − β_i) v_i − Σ_{t=j+1}^{i−1} (β_t − β_{t+1}) v_{t+1}
≤ (β_j − β_i) v_i − Σ_{t=j+1}^{i−1} (β_t − β_{t+1}) v_i = (β_j − β_{j+1}) v_i
≤ (β_j − β_{j+1}) v_{j+1} ≤ (α_j − α_{j+1}) b_{j+1}" (footnote 10: local envy-freeness with
regard to the position directly above implies envy-freeness with regard to all higher
positions).

In the sorted frame (`v`, `b` non-increasing, identity ranking): if (27) holds for every
`i ∈ {2, …, n}`, then (25) holds for all `j < i`.

**Formalization Note.** 0-based indices; `padBids b t` is `b_{t+1}`, `0` past the end. The page
applies this to the pessimal profile (26); the statement assumes only (27). -/
theorem local_envy_free_imp_25 {k n : ℕ} (hkn : k ≤ n) {α β : ℕ → ℝ} (hα : IsPosVec k α)
    (hβ : IsPosVec k β) {v b : Fin n → ℝ} (hv0 : ∀ i, 0 ≤ v i) (hv : Antitone v)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Antitone b)
    (h27 : ∀ (i : ℕ) (h : i + 1 < n),
      (β i - β (i + 1)) * v ⟨i + 1, h⟩ ≤ (α i - α (i + 1)) * padBids b (i + 1)) :
    ∀ i j : Fin n, j < i →
      (β j - β i) * v i -
          ∑ t ∈ Finset.Ico ((j : ℕ) + 1) i, (α t - α (t + 1)) * padBids b (t + 1)
        ≤ (α j - α (j + 1)) * padBids b (j + 1) := by sorry

end NontruthfulPA

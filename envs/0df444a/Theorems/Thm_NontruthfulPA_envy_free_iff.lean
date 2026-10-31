-- Prove2me | Theorems.Thm_NontruthfulPA_envy_free_iff
-- name    : NontruthfulPA.envy_free_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:16.087559+00:00
-- url     : https://prove2.me/theorems/440202e9-57cd-47ed-862c-062216b85508
-- title:
--   (24)–(25) — envy-freeness conditions for sorted $\alpha$-VCG profiles
-- statement:
--   There are $k$ positions and $n \ge k$ bidders. The position vectors $\alpha, \beta \in \mathbb R^k_\ge$ are positive and non-increasing, with $\alpha_j = \beta_j = 0$ for $j > k$; bidder $i$ values position $j$ at $\beta_j v_i$ with $v_i \ge 0$. Bids are $b \in [0,\infty)^n$, and $b_{(t)}$ denotes the $t$-th highest bid, with $b_{(t)} = 0$ for $t > n$.
--
--   Assume $v_1 \ge \dots \ge v_n$ and let $b_1 \ge \dots \ge b_n \ge 0$, bidder $i$ in position $i$, $b_t = 0$ for $t > n$. Then $b$ is envy-free (22) under the $\alpha$-VCG payments if and only if (24) holds for all $i < j$ and, for all $j < i$,
--   $$(\alpha_j - \alpha_{j+1})\, b_{j+1} \ \ge\ (\beta_j - \beta_i)\, v_i - \sum_{t=j+1}^{i-1} (\alpha_t - \alpha_{t+1})\, b_{t+1}. \tag{25}$$
--
--   Envy-freeness replaces the deviation price of an upward move, which appears in (23), by the current price of the target position. Varian calls profiles satisfying (24) and (25) symmetric equilibria.
--
--   **Formalization Note** Bidders are `Fin n` and positions are 0-based ranks (rank $r$ is position $r+1$); $\alpha, \beta$ are functions on $\mathbb N$ that vanish from index $k$ on; the bids in rank order are padded by $0$ past rank $n$.
--
--   Differences from the source:
--   - generalization: a sorted profile is envy-free if (24) and (25) hold → if and only if; reason: (22) for a pair of positions is exactly (24) or (25), so the converse holds too; the equivalence contains the page's implication
--   - reading: bid profiles b ∈ ℝ^n (p.6) → bids b_i ≥ 0; reason: mechanisms charge non-negative payments (p.6) and §3.1 uses b_3 ≥ 0 (p.8); with negative bids the payments could be negative
--   - reading: v ∈ ℝ^n with β_j v_i ≥ 0 the value for position j (p.6) → v_i ≥ 0; reason: β_j > 0 for j ≤ k, so β_j v_i ≥ 0 is v_i ≥ 0
--   - encoding: WLOG v_1 ≥ ⋯ ≥ v_n and bidder i is assigned position i (p.11) → v and b antitone on Fin n and the identity ranking Equiv.refl; reason: the paper's sorted frame, written out
--   - encoding: bidders and positions 1,…,n; α, β ∈ ℝ^k with α_j = β_j = 0 for j > k; b_(i) = 0 for i > n → Fin n with 0-based ranks; α, β : ℕ → ℝ positive and non-increasing below k and 0 from k on; rank lists ℕ → ℝ padded by 0; reason: Lean convention; same instances
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, §3.2, (25), p.11

import Mathlib
import Definitions.Def_NontruthfulPA_Model

namespace NontruthfulPA

/-- **Envy-freeness conditions (24)–(25)**, Dütting–Fischer–Parkes, *Non-Truthful Position
Auctions Are More Robust to Misspecification*, arXiv:1602.07593v4, §3.2, p.11: "Specializing
(22), a bid profile b with b1 ≥ ⋯ ≥ bn is envy-free if for all i, j ∈ {1,…,n}, in addition to
(24) and instead of (23),
(α_j − α_{j+1}) b_{j+1} ≥ (β_j − β_i) v_i − Σ_{t=j+1}^{i−1} (α_t − α_{t+1}) b_{t+1} if j < i. (25)"

Stated as an equivalence for the α-VCG payments, in the sorted frame of p.11.

**Formalization Note.** 0-based indices as in `vcg_equilibrium_iff`; `padBids b t` is
`b_{t+1}`, `0` past the end. Envy-freeness is (22) with the α-VCG payments of the identity
ranking. The page states "if"; the specialization is exact, so the equivalence is posed. -/
theorem envy_free_iff {k n : ℕ} (hkn : k ≤ n) {α β : ℕ → ℝ} (hα : IsPosVec k α)
    (hβ : IsPosVec k β) {v b : Fin n → ℝ} (hv0 : ∀ i, 0 ≤ v i) (hv : Antitone v)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Antitone b) :
    IsEnvyFree (payV k α) β v b (Equiv.refl (Fin n)) ↔
      ((∀ i j : Fin n, i < j →
          (α i - α (i + 1)) * padBids b (i + 1) ≤
            (β i - β j) * v i -
              ∑ t ∈ Finset.Ico ((i : ℕ) + 1) j, (α t - α (t + 1)) * padBids b (t + 1)) ∧
        (∀ i j : Fin n, j < i →
          (β j - β i) * v i -
              ∑ t ∈ Finset.Ico ((j : ℕ) + 1) i, (α t - α (t + 1)) * padBids b (t + 1)
            ≤ (α j - α (j + 1)) * padBids b (j + 1))) := by sorry

end NontruthfulPA

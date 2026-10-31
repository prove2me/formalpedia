-- Prove2me | Theorems.Thm_NontruthfulPA_lemma_2
-- name    : NontruthfulPA.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:15.432529+00:00
-- url     : https://prove2.me/theorems/55afa922-43d4-4d79-a1c8-b684552e1906
-- title:
--   Lemma 2 — $b^S$ is sorted and $\alpha$-GSP payments at $b^S$ equal $\alpha$-VCG payments at $b$
-- statement:
--   Let $\alpha \in \mathbb R^k_\ge$ (positive and non-increasing, $\alpha_j = 0$ for $j > k$), $n \ge k$, and let $b_1 \ge \dots \ge b_n \ge 0$. Let $b^S \in \mathbb R^n$ be defined for all $i \in \{1, \dots, n\}$ by
--   $$b^S_i = \begin{cases} b^S_2 & \text{if } i = 1, \\ p^V_{i-1}(b)/\alpha_{i-1} & \text{if } i \in \{2, \dots, k+1\} \text{ and } \alpha_{i-1} > 0, \\ 0 & \text{otherwise.} \end{cases}$$
--   Then
--
--   1. $b^S_1 \ge \dots \ge b^S_n$, and
--   2. for all $i \in \{1, \dots, n\}$, $p^S_i(b^S) = p^V_i(b)$,
--
--   where both payments are taken with bidder $i$ in position $i$. So the $\alpha$-GSP mechanism at $b^S$ produces the same allocation and the same payments as the $\alpha$-VCG mechanism at $b$; this is the second step of the proof of Theorem 1.
--
--   **Formalization Note** Bidders are 0-based; the bids in rank order are padded by $0$ past rank $n$. The ranking is the identity on both sides, which orders $b$ and, by item 1, $b^S$ (the tie $b^S_1 = b^S_2$ is resolved by the ranking).
--
--   Differences from the source:
--   - generalization: α, β ∈ ℝ^k_≥ and v, b ∈ ℝ^n_≥ (positive, non-increasing) → α ∈ ℝ^k_≥ and b non-negative and non-increasing; β and v do not appear; reason: neither conclusion involves β or v, and the proof never uses positivity of b; the source's case is an instance
--   - encoding: bidders and positions 1,…,n; α, β ∈ ℝ^k with α_j = β_j = 0 for j > k; b_(i) = 0 for i > n → Fin n with 0-based ranks; α, β : ℕ → ℝ positive and non-increasing below k and 0 from k on; rank lists ℕ → ℝ padded by 0; reason: Lean convention; same instances
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, Lemma 2, p.13

import Mathlib
import Definitions.Def_NontruthfulPA_Model
import Definitions.Def_NontruthfulPA_GSPImage

namespace NontruthfulPA

/-- **Lemma 2**, Dütting–Fischer–Parkes, *Non-Truthful Position Auctions Are More Robust to
Misspecification*, arXiv:1602.07593v4, p.13: "Let α, β ∈ ℝ^k_≥ and v, b ∈ ℝ^n_≥. Let b^S ∈ ℝ^n
such that for all i ∈ {1,…,n}, b^S_i = b^S_2 if i = 1, p^V_{i−1}(b)/α_{i−1} if i ∈ {2,…,k+1}
and α_{i−1} > 0, 0 otherwise. Then b^S_1 ≥ ⋯ ≥ b^S_n and for all i ∈ {1,…,n},
p^S_i(b^S) = p^V_i(b)."

**Formalization Note.** `b^S` is `gspImage k α b`. Both payments are taken with the identity
ranking (bidder `i` at rank `i`, 0-based), which is an allocation of `g` for `b` and, by the
first conclusion, for `b^S` (the tie `b^S_1 = b^S_2` is resolved by the ranking).
`padBids x` lists `x` by rank, `0` past the end. `b ∈ ℝ^n_≥` is relaxed to non-negative and
non-increasing; `β` and `v` do not enter the statement. -/
theorem lemma_2 {k n : ℕ} (hkn : k ≤ n) {α : ℕ → ℝ} (hα : IsPosVec k α) {b : Fin n → ℝ}
    (hb0 : ∀ i, 0 ≤ b i) (hb : Antitone b) :
    Antitone (gspImage k α b) ∧
      ∀ i : Fin n, payS α (padBids (gspImage k α b)) i = payV k α (padBids b) i := by sorry

end NontruthfulPA

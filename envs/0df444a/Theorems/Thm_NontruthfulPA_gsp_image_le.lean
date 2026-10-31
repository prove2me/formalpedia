-- Prove2me | Theorems.Thm_NontruthfulPA_gsp_image_le
-- name    : NontruthfulPA.gsp_image_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:07.258951+00:00
-- url     : https://prove2.me/theorems/ab12c8ea-95d4-4de3-b750-d5f0d77fcab5
-- title:
--   (28) — $b^S_i \le b_i$ for $i \in \{2, \dots, k+1\}$
-- statement:
--   Let $\alpha \in \mathbb R^k_\ge$ (positive and non-increasing, $\alpha_j = 0$ for $j > k$), $n \ge k$, and let $b_1 \ge \dots \ge b_n \ge 0$, with $b_t = 0$ for $t > n$. Let $b^S$ be the $\alpha$-GSP image of $b$ from Lemma 2. Since $\alpha$ is positive on the $k$ positions, $\min\{i : \alpha_i = 0\} = k + 1$, and for all $i \in \{2, \dots, k+1\}$ with $i \le n$,
--   $$b^S_i = \frac{p^V_{i-1}(b)}{\alpha_{i-1}} = \frac{\sum_{t=i-1}^{k} (\alpha_t - \alpha_{t+1})\, b_{t+1}}{\alpha_{i-1}} \ \le\ \frac{\sum_{t=i-1}^{k} (\alpha_t - \alpha_{t+1})\, b_i}{\alpha_{i-1}} = b_i. \tag{28}$$
--
--   This is the first step of the proof that $b^S$ is sorted.
--
--   **Formalization Note** Bidders are 0-based: index $i \in \{1, \dots, k\}$ is the paper's $i + 1$. Only the inequality $b^S_i \le b_i$ is stated; the intermediate equalities are the definitions.
--
--   Differences from the source:
--   - generalization: v, b ∈ ℝ^n_≥ (positive, non-increasing) and β ∈ ℝ^k_≥ → b non-negative and non-increasing; β and v do not appear; reason: the inequality involves neither β nor v, and the proof never uses positivity of b; the source's case is an instance
--   - encoding: bidders and positions 1,…,n; α, β ∈ ℝ^k with α_j = β_j = 0 for j > k; b_(i) = 0 for i > n → Fin n with 0-based ranks; α, β : ℕ → ℝ positive and non-increasing below k and 0 from k on; rank lists ℕ → ℝ padded by 0; reason: Lean convention; same instances
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, proof of Lemma 2, (28), p.13

import Mathlib
import Definitions.Def_NontruthfulPA_Model
import Definitions.Def_NontruthfulPA_GSPImage

namespace NontruthfulPA

/-- **(28)**, Dütting–Fischer–Parkes, *Non-Truthful Position Auctions Are More Robust to
Misspecification*, arXiv:1602.07593v4, proof of Lemma 2, p.13: with `j = min{i : α_i = 0}`,
"for all i ∈ {2,…,j},
b^S_i = p^V_{i−1}/α_{i−1} = Σ_{t=i−1}^{k} (α_t − α_{t+1}) b_{t+1} / α_{i−1}
≤ Σ_{t=i−1}^{k} (α_t − α_{t+1}) b_i / α_{i−1} = (α_{i−1} − α_{k+1}) b_i / α_{i−1} = b_i, (28)".

For a non-negative non-increasing profile `b` and `α ∈ ℝ^k_≥` (so `j = k + 1`):
`b^S_i ≤ b_i` for every bidder `i ∈ {2, …, k+1}` with `i ≤ n`.

**Formalization Note.** 0-based: bidder `i : Fin n` with `1 ≤ i ≤ k` is the paper's
`i + 1 ∈ {2, …, k+1}`. `b ∈ ℝ^n_≥` is relaxed to non-negative and non-increasing. -/
theorem gsp_image_le {k n : ℕ} (hkn : k ≤ n) {α : ℕ → ℝ} (hα : IsPosVec k α) {b : Fin n → ℝ}
    (hb0 : ∀ i, 0 ≤ b i) (hb : Antitone b) :
    ∀ i : Fin n, 1 ≤ (i : ℕ) → (i : ℕ) ≤ k → gspImage k α b i ≤ b i := by sorry

end NontruthfulPA

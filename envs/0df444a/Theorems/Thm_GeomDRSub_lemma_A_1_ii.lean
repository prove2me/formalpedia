-- Prove2me | Theorems.Thm_GeomDRSub_lemma_A_1_ii
-- name    : GeomDRSub.lemma_A_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:10:15.351885+00:00
-- url     : https://prove2.me/theorems/b5882cd2-d614-4eb7-bece-537c7946a40d
-- title:
--   Lemma A.1(ii) — summation by parts
-- statement:
--   Let $n\ge1$ and let $w_1,\dots,w_n$ and $a_0,\dots,a_n$ be real numbers. Then
--   $$
--   \sum_{k=1}^n w_k(a_k-a_{k-1})=w_na_n-w_1a_0-\sum_{k=1}^{n-1}(w_{k+1}-w_k)a_k .
--   $$
--   If moreover $0\le w_1\le\cdots\le w_n\le W$ and $a_k\ge0$ for all $k$, then the sum on the left is at most $W a_n$.
--
--   This bounds the upper-path sum in the proof of Lemma 4.1, where the weights $\mu_{\pi(k)}$ are nondecreasing.
--
--   Differences from the source:
--   - encoding: scalars w_1..w_n, a_0..a_n → sequences w a : ℕ → ℝ with 1 ≤ n (only indices 1..n of w and 0..n of a matter); reason: w_1 and w_n exist only for n ≥ 1; the identity is undefined at n = 0
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Lemma A.1(ii), p.65, Eq. (270)

import Mathlib

namespace GeomDRSub

/-- **Lemma A.1(ii) (summation by parts).** Aggarwal–Lu, arXiv:2610.00545, Appendix A, p.65:
"For scalars `w₁, …, wₙ` and `a₀, …, aₙ`,
`∑_{k=1}^n w_k(a_k − a_{k−1}) = wₙaₙ − w₁a₀ − ∑_{k=1}^{n−1} (w_{k+1} − w_k)a_k`. (270)
If `0 ≤ w₁ ≤ ⋯ ≤ wₙ ≤ W` and `a_k ≥ 0` for all `k`, the sum on the left is at most `Waₙ`."

Both the identity and the inequality are stated.

**Formalization Note.** The finite sequences are functions `ℕ → ℝ` of which only the indices
`1..n` of `w` and `0..n` of `a` matter. The statement assumes `1 ≤ n`, since `w₁` and `wₙ` only
exist for `n ≥ 1`. -/
theorem lemma_A_1_ii (n : ℕ) (hn : 1 ≤ n) (w a : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 n, w k * (a k - a (k - 1)) =
        w n * a n - w 1 * a 0 - ∑ k ∈ Finset.Icc 1 (n - 1), (w (k + 1) - w k) * a k) ∧
      ∀ W : ℝ, 0 ≤ w 1 → (∀ k, 1 ≤ k → k < n → w k ≤ w (k + 1)) → w n ≤ W →
        (∀ k ≤ n, 0 ≤ a k) →
        ∑ k ∈ Finset.Icc 1 n, w k * (a k - a (k - 1)) ≤ W * a n := by sorry

end GeomDRSub

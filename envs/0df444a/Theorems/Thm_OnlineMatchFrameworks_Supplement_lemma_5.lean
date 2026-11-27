-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_Supplement_lemma_5
-- name    : OnlineMatchFrameworks.Supplement.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:27:34.151335+00:00
-- url     : https://prove2.me/theorems/2145720b-f981-5937-a6e6-4c33d1365572
-- title:
--   Lemma 5: the truncated product sum is at least half the total
-- statement:
--   Let $\bar\theta\ge1$ and let $x_1,\dots,x_{\bar\theta}$ be nonnegative reals with $x_{\bar\theta}>0$. Then
--
--   $$
--   \sum_{\theta=1}^{\bar\theta}x_\theta\prod_{\theta'=1}^{\theta-1}\max\Bigl\{1-\frac{x_{\theta'}}{x_{\theta'+1}+\dots+x_{\bar\theta}},\,0\Bigr\}\ \ge\ \frac12\sum_{\theta=1}^{\bar\theta}x_\theta .
--   $$
--
--   In the paper $x_\theta=x^*_{j\theta}$ for a fixed item $j$ and an optimal solution of LP (5), and the left side bounds from below the probability that the algorithm really probes $j$. The inequality closes the proof of the $1/2$-approximation for an arbitrary patience distribution.
--
--   Differences from the source:
--   - generalization: x* a column of an optimal solution of LP (5), θ̄ the largest index with x*_θ > 0 (p.45) → any nonnegative sequence x_1, …, x_n with x_n > 0; reason: such a column, truncated at θ̄, is one such sequence
--   - reading: the algorithm’s probability of probing any offline node in a non-simulated fashion is at least half the LP total; "That is," the displayed inequality → the displayed inequality; reason: the lemma defines its claim by the display, and the link to the algorithm is (17)–(18) in the proof of Theorem 6
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Appendix A, Lemma 5, p.45

import Mathlib

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

/-- **Lemma 5.** arXiv:1907.03963v6, Appendix A, Lemma 5, p.45:
`∑_{θ=1}^{θ̄} x*_θ ∏_{θ'=1}^{θ-1} max{1 - x*_{θ'}/(x*_{θ'+1} + ⋯ + x*_θ̄), 0} ≥ ½ ∑_{θ=1}^{θ̄} x*_θ`.

**Formalization Note.** `x` is the column `x*_{jθ}` of a fixed item `j`, and `n` is `θ̄`, "the maximum
index θ for which x*_θ > 0" (p.45). Only `x ≥ 0` and `x n > 0` are used, so the statement is for any
such sequence. Every denominator is positive, since it contains `x n`. -/
theorem lemma_5 (n : ℕ) (hn : 1 ≤ n) (x : ℕ → ℝ)
    (hx : ∀ θ ∈ Finset.Icc 1 n, 0 ≤ x θ) (hlast : 0 < x n) :
    1 / 2 * ∑ θ ∈ Finset.Icc 1 n, x θ ≤
      ∑ θ ∈ Finset.Icc 1 n, x θ *
        ∏ θ' ∈ Finset.Ico 1 θ,
          max (1 - x θ' / ∑ k ∈ Finset.Icc (θ' + 1) n, x k) 0 := by sorry

end OnlineMatchFrameworks.Supplement

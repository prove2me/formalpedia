-- Prove2me | Theorems.Thm_OrderedExperts_lemma_8
-- name    : OrderedExperts.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:32:59.780996+00:00
-- url     : https://prove2.me/theorems/887d3d11-bb03-4138-be0c-a7de5f9ead2f
-- title:
--   Lemma 8 — discrete integral bounds
-- statement:
--   Let $(s_j)$ be real numbers with $0\le s_{b-1}<s_b<s_{b+1}<\cdots$ and set $\delta_j=s_j-s_{j-1}$. Then
--   $$
--   \sum_{j\ge b}\frac{\delta_j}{s_j^2}\le\frac{2}{s_b}.
--   $$
--   Moreover there is an absolute constant $C>0$ such that for every such sequence and every $\alpha>0$,
--   $$
--   \sum_{j\ge b}\frac{\delta_j}{s_j^2(\alpha+s_j)^2}\le\frac{C}{s_b(\alpha+s_b)^2}.
--   $$
--
--   These comparisons of sums with integrals bound the edge loads of the endpoint flow estimator (Lemma 4).
--
--   **Formalization Note** The sequence is indexed by $\mathbb N$ with $b\ge1$; the series of nonnegative terms are bounded through all their partial sums $\sum_{j=b}^N$.
--
--   Differences from the source:
--   - encoding: series $\sum_{j\ge b}$ → every partial sum $\sum_{j=b}^N$; reason: the terms are nonnegative, so the bounds are equivalent
--   - encoding: $O(1/(s_b(\alpha+s_b)^2))$ → one absolute constant $C>0$ chosen before the sequence, $b$ and $\alpha$; reason: meaning of $O(\cdot)$ in the paper (the proof gives $C=2$)
--   - encoding: index $b$ with a term $s_{b-1}$ → $b\ge1$ in $\mathbb N$; reason: reindexing; same instances
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Lemma 8, p.18; Appendix A.4, p.18

import Mathlib
open Finset

namespace OrderedExperts

/-- **Lemma 8 (Discrete integral bounds).** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Lemma 8, p.18: "Let
`0 ≤ sb−1 < sb < sb+1 < · · ·` and `δj = sj − sj−1`. Then `Σ_{j≥b} δj/s²j ≤ 2/sb`. For every `α > 0`,
`Σ_{j≥b} δj/(s²j(α + sj)²) = O(1/(sb(α + sb)²))`."

For a real sequence with `0 ≤ s(b−1) < s(b) < s(b+1) < ⋯` (`b ≥ 1`), every partial sum
`Σ_{j=b}^N (s j − s(j−1))/s j²` is at most `2/s b`; and there is an absolute constant `C > 0` such that
for every such sequence and every `α > 0`, every partial sum
`Σ_{j=b}^N (s j − s(j−1))/(s j² (α + s j)²)` is at most `C/(s b (α + s b)²)`.

**Formalization Note.** The series of nonnegative terms is bounded through all its partial sums,
which is equivalent; the sequence is indexed by `ℕ` from `b − 1 ≥ 0`; `O(·)` is one absolute
constant, quantified before the sequence, `b` and `α`. -/
theorem lemma_8 :
    (∀ (s : ℕ → ℝ) (b : ℕ), 1 ≤ b → 0 ≤ s (b - 1) → (∀ j, b ≤ j → s (j - 1) < s j) →
      ∀ N : ℕ, ∑ j ∈ Icc b N, (s j - s (j - 1)) / s j ^ 2 ≤ 2 / s b) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℕ → ℝ) (b : ℕ), 1 ≤ b → 0 ≤ s (b - 1) →
      (∀ j, b ≤ j → s (j - 1) < s j) → ∀ α : ℝ, 0 < α → ∀ N : ℕ,
        ∑ j ∈ Icc b N, (s j - s (j - 1)) / (s j ^ 2 * (α + s j) ^ 2) ≤
          C / (s b * (α + s b) ^ 2) := by sorry

end OrderedExperts

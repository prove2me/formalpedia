-- Prove2me | Theorems.Thm_OddPerfectNumber_nielsen_comparison
-- name    : OddPerfectNumber.nielsen_comparison
-- status  : Proved
-- author  : @curiyu
-- created : 2026-09-08T04:33:59.612164+00:00
-- url     : https://prove2.me/theorems/c381c75e-0812-4015-8fce-ac263f4fd463
-- title:
--   Nielsen comparison for $\prod(1-1/z)$ under partial-product dominance
-- statement:
--   This is Lemma 1.2 of Nielsen (2015), the product comparison lemma behind the odd-perfect upper bounds.
--
--   Let $k \ge 1$ be an integer and let $1 < z_1 \le \cdots \le z_k$ and $1 < y_1 \le \cdots \le y_k$ be non-decreasing real sequences satisfying the partial-product dominance
--   $$
--   \prod_{i=1}^{l} z_i \le \prod_{i=1}^{l} y_i
--   $$
--   for every $1 \le l \le k$. Then
--   $$
--   \prod_{i=1}^{k}\left(1-\frac{1}{z_i}\right) \le \prod_{i=1}^{k}\left(1-\frac{1}{y_i}\right),
--   $$
--   with equality if and only if $z_i = y_i$ for every $i$.
--
--   This lemma is the structural parent of the two-variable perturbation estimate and the calibrating product identity: together they drive the maximality argument in Lemma 1 of Nielsen (2003), which in turn feeds the prime-set extensions in the proof of Theorem 1.
--
--   **Formalization Note** Sequences are $0$-indexed in Lean ($z, y : \mathbb{N} \to \mathbb{R}$ with indices $i < k$), products are over `Finset.range`, and positivity $1 < z_i$, $1 < y_i$ plus both monotonicity hypotheses are explicit.
-- source:
--   P. P. Nielsen, Odd perfect numbers, Diophantine equations, and upper bounds, Math. Comp. 84 (2015), Lemma 1.2; see also M. Cook, comparison lemma (cf. Nielsen 2003 INTEGERS #A14, Section 2); author's version https://mathdept.byu.edu/~pace/BestBound_web.pdf

import Mathlib

namespace OddPerfectNumber

theorem nielsen_comparison (k : ℕ) (z y : ℕ → ℝ) (hk : 0 < k)
    (hz1 : ∀ i, i < k → 1 < z i)
    (hy1 : ∀ i, i < k → 1 < y i)
    (hzmono : ∀ i j, i < j → j < k → z i ≤ z j)
    (hymono : ∀ i j, i < j → j < k → y i ≤ y j)
    (hpart : ∀ l, 1 ≤ l → l ≤ k →
      Finset.prod (Finset.range l) (fun i => z i) ≤
        Finset.prod (Finset.range l) (fun i => y i)) :
    Finset.prod (Finset.range k) (fun i => (1 - 1 / z i)) ≤
        Finset.prod (Finset.range k) (fun i => (1 - 1 / y i)) ∧
      (Finset.prod (Finset.range k) (fun i => (1 - 1 / z i)) =
        Finset.prod (Finset.range k) (fun i => (1 - 1 / y i)) ↔
        ∀ i, i < k → z i = y i) := by
  sorry

end OddPerfectNumber

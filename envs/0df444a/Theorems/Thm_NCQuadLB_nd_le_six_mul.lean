-- Prove2me | Theorems.Thm_NCQuadLB_nd_le_six_mul
-- name    : NCQuadLB.nd_le_six_mul
-- status  : Proved
-- author  : @iris
-- created : 2026-11-10T20:27:28.640016+00:00
-- url     : https://prove2.me/theorems/c3cc3423-683f-4c5b-b3ca-6d6ff17e60a6
-- title:
--   Proof of Theorem 4.2 — $S\ge nd/(e(d+1)^{1/d})\ge(nd)/6$
-- statement:
--   Let $n\ge2$, $d\ge1$, and let $S$ be a natural number with $n^d\le\sum_{k=0}^d\binom Sk$. Then:
--
--   1. if $d\le S/2$, $$S\ge\frac{nd}{e(d+1)^{1/d}}\ge\frac{nd}{6};$$
--   2. in every case, $S\ge nd/6$.
--
--   With the counting inequality for circuits, this is the numerical half of Theorem 4.2.
--
--   **Formalization Note** $S\ge nd/6$ is stated as $nd\le6S$ in $\mathbb N$; $e=\exp1$ and $(d+1)^{1/d}$ is the real power.
--
--   Differences from the source:
--
--   - generalization: $S$ the number of product gates of a circuit computing $\mathrm{Pal}_{n,d}$ → any natural number $S$ with $n^d\le\sum_{k=0}^d\binom Sk$; reason: the conclusion uses only this inequality, which every such circuit satisfies (the counting milestone)
--   - generalization: "$S\ge(nd)/6$" in the case $d\le S/2$, and "$S=\Omega(nd)$" in the case $S/2<d$ → $nd\le6S$ in both cases; reason: an explicit constant implies $\Omega(nd)$; the source's case-2 intermediate "this implies $n\le5$" is false for $d\le3$ and is not stated
--   - encoding: $d\le S/2$; $e$; $S\ge(nd)/6$ → $2d\le S$; $\exp1$; $nd\le6S$ in $\mathbb N$; reason: the same conditions and values
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), proof of Theorem 4.2, p.8 ("Therefore, S ≥ nd/(e(d+1)^{1/d}) ≥ (nd)/6, and we're done.")

import Mathlib

namespace NCQuadLB

/-- **Proof of Theorem 4.2, the numerical conclusion** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, p.8). Let `n ≥ 2`, `d ≥ 1` and let `S`
be a natural number with `n^d ≤ ∑_{k=0}^d (S choose k)`. If `d ≤ S/2` then
`S ≥ nd/(e(d+1)^{1/d}) ≥ (nd)/6`; and in every case `S ≥ (nd)/6`.

**Formalization Note** `S` is any natural number satisfying the counting inequality (for a circuit
computing `Pal_{n,d}`, its number of product gates, by the counting milestone). `d ≤ S/2` is `2d ≤ S`,
`e = Real.exp 1`, `(d+1)^{1/d}` is the real power. `S ≥ (nd)/6` is stated as `nd ≤ 6S` in `ℕ`. -/
theorem nd_le_six_mul (n d S : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hcount : n ^ d ≤ ∑ k ∈ Finset.range (d + 1), S.choose k) :
    (2 * d ≤ S →
      ((n : ℝ) * d) / (Real.exp 1 * ((d : ℝ) + 1) ^ ((1 : ℝ) / d)) ≤ S ∧
        ((n : ℝ) * d) / 6 ≤ ((n : ℝ) * d) / (Real.exp 1 * ((d : ℝ) + 1) ^ ((1 : ℝ) / d))) ∧
      n * d ≤ 6 * S := by sorry

end NCQuadLB

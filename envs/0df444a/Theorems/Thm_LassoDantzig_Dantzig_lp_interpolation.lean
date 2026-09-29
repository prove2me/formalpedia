-- Prove2me | Theorems.Thm_LassoDantzig_Dantzig_lp_interpolation
-- name    : LassoDantzig.Dantzig.lp_interpolation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:16:40.971582+00:00
-- url     : https://prove2.me/theorems/60f34386-7844-4907-a7df-45027bfc5da8
-- title:
--   Proof of Theorem 7.1 — interpolation $\sum a_j^p\le b_1^{2-p}b_2^{p-1}$ for $1<p\le2$
-- statement:
--   Let $a_1,\dots,a_M\ge0$ and $b_1,b_2\in\mathbb R$ with
--
--   $$
--   \sum_{j=1}^Ma_j\le b_1,\qquad\sum_{j=1}^Ma_j^2\le b_2 .
--   $$
--
--   Then for every real $p$ with $1<p\le2$,
--
--   $$
--   \sum_{j=1}^Ma_j^p\le\Big(\sum_{j=1}^Ma_j\Big)^{2-p}\Big(\sum_{j=1}^Ma_j^2\Big)^{p-1}\le b_1^{2-p}b_2^{p-1}.
--   $$
--
--   Applied to $a_j=|\hat\beta_{D,j}-\beta^*_j|$ with the $\ell_1$ bound (7.4) and the $\ell_2$ bound (B.29), it turns the two endpoint rates into the $\ell_p$ rate (7.6) of Theorem 7.1.
--
--   **Formalization Note** Powers with real exponent are `Real.rpow`; for $p=2$ the factor $(\sum_j a_j)^{0}$ equals 1 by convention, including when the sum is 0.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 28, Appendix B, proof of Theorem 7.1, display after (B.29)

import Mathlib

namespace LassoDantzig.Dantzig

/-- Proof of Theorem 7.1, last display (p. 28): if `aⱼ ≥ 0`, `∑ⱼ aⱼ ≤ b₁` and
`∑ⱼ aⱼ² ≤ b₂`, then for every real `1 < p ≤ 2`,
`∑ⱼ aⱼ^p ≤ (∑ⱼ aⱼ)^{2−p} (∑ⱼ aⱼ²)^{p−1} ≤ b₁^{2−p} b₂^{p−1}`. -/
theorem lp_interpolation {M : ℕ} (a : Fin M → ℝ) (ha : ∀ j, 0 ≤ a j) (b1 b2 : ℝ)
    (h1 : ∑ j, a j ≤ b1) (h2 : ∑ j, a j ^ 2 ≤ b2) (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∑ j, a j ^ p ≤ (∑ j, a j) ^ (2 - p) * (∑ j, a j ^ 2) ^ (p - 1) ∧
    (∑ j, a j) ^ (2 - p) * (∑ j, a j ^ 2) ^ (p - 1) ≤ b1 ^ (2 - p) * b2 ^ (p - 1) := by sorry

end LassoDantzig.Dantzig

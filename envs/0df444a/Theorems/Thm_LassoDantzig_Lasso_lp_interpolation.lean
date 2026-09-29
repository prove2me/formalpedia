-- Prove2me | Theorems.Thm_LassoDantzig_Lasso_lp_interpolation
-- name    : LassoDantzig.Lasso.lp_interpolation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:21:35.605297+00:00
-- url     : https://prove2.me/theorems/9c3b6e4a-ea83-466a-8b08-fa4a337d7ba4
-- title:
--   Appendix B, display after (B.29) — interpolation of $\ell_p$ between $\ell_1$ and $\ell_2$
-- statement:
--   Let $a_1,\dots,a_M\ge0$ and $b_1,b_2\in\mathbb R$ with
--   $$
--   \sum_{j=1}^Ma_j\le b_1,\qquad\sum_{j=1}^Ma_j^2\le b_2 .
--   $$
--   Then for every $1<p\le2$,
--   $$
--   \sum_{j=1}^Ma_j^p\le b_1^{2-p}\,b_2^{p-1}.
--   $$
--
--   Applied to $a_j=|\hat\beta_{j,L}-\beta^*_j|$ with the $\ell_1$ bound (7.7) and the $\ell_2$ bound from (B.28)–(B.29), this yields the $\ell_p$ bound (7.10).
--
--   **Formalization Note** Powers with real exponents are real powers of non-negative numbers ($b_1,b_2\ge0$ follows from the hypotheses).
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 28, Appendix B, proof of Theorem 7.1, display after (B.29)

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- The ℓp interpolation, p. 28 (display after (B.29)): if `aⱼ ≥ 0`, `∑ⱼ aⱼ ≤ b₁` and
`∑ⱼ aⱼ² ≤ b₂`, then `∑ⱼ aⱼ^p ≤ b₁^{2−p} b₂^{p−1}` for every `1 < p ≤ 2`. -/
theorem lp_interpolation {M : ℕ} (a : Fin M → ℝ) (ha : ∀ j, 0 ≤ a j) (b1 b2 : ℝ)
    (h1 : ∑ j, a j ≤ b1) (h2 : ∑ j, a j ^ 2 ≤ b2) (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∑ j, a j ^ p ≤ b1 ^ (2 - p) * b2 ^ (p - 1) := by sorry

end LassoDantzig.Lasso

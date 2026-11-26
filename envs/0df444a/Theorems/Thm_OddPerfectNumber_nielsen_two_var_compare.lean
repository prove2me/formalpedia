-- Prove2me | Theorems.Thm_OddPerfectNumber_nielsen_two_var_compare
-- name    : OddPerfectNumber.nielsen_two_var_compare
-- status  : Proved
-- author  : @curiyu
-- created : 2026-09-08T04:25:17.481261+00:00
-- url     : https://prove2.me/theorems/93959a06-6d37-439c-bb8a-49b5397751d8
-- title:
--   Two-variable perturbation $\\prod(1-1/x)$ iff $w \\le x_2/x_1$
-- statement:
--   This is Lemma 1.1 of Nielsen 2015 (Section 1), the two-variable engine behind the product comparison used in all the odd-perfect upper bounds.
--
--   Let $x_1, x_2, w$ be positive reals with $w < 1$. Rescale the pair $(x_1, x_2)$ to $(w x_1, x_2/w)$, shrinking the first factor and growing the second so their product is unchanged. Then
--   $$
--   \left(1-\frac{1}{x_1}\right)\left(1-\frac{1}{x_2}\right) \ge \left(1-\frac{1}{w x_1}\right)\left(1-\frac{1}{x_2/w}\right)
--   $$
--   holds if and only if $w \le x_2/x_1$. In particular the difference of the two sides factors as $(1-w)(x_2-wx_1)/(wx_1x_2)$, so equality holds exactly at $w = x_2/x_1$, and the inequality is strict whenever $x_1 \le x_2$ (since then $x_2/x_1 \ge 1 > w$).
--
--   This is the perturbation step in the proof of the product comparison lemma (Lemma 1.2): at a minimizing tuple, no such product-preserving perturbation can decrease the objective, which forces the minimizer to coincide with the comparison sequence.
--
--   **Formalization Note** All divisions are in $\mathbb{R}$; positivity of $x_1, x_2, w$ and $w < 1$ are explicit hypotheses.
-- source:
--   P. P. Nielsen, Odd perfect numbers, Diophantine equations, and upper bounds, Math. Comp. 84 (2015), Lemma 1.1; author's version https://mathdept.byu.edu/~pace/BestBound_web.pdf

import Mathlib

namespace OddPerfectNumber

theorem nielsen_two_var_compare (x1 x2 w : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hw0 : 0 < w) (hw1 : w < 1) :
    (1 - 1 / x1) * (1 - 1 / x2) ≥ (1 - 1 / (w * x1)) * (1 - 1 / (x2 / w)) ↔ w ≤ x2 / x1 := by
  sorry

end OddPerfectNumber

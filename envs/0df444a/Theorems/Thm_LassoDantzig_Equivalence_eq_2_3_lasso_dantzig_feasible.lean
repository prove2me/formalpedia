-- Prove2me | Theorems.Thm_LassoDantzig_Equivalence_eq_2_3_lasso_dantzig_feasible
-- name    : LassoDantzig.Equivalence.eq_2_3_lasso_dantzig_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:48:56.098258+00:00
-- url     : https://prove2.me/theorems/e34e68bc-47b2-4435-9baa-54bf9f5e5b7e
-- title:
--   Eq. (2.3) — every Lasso solution satisfies the Dantzig constraint
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ with $n\ge1$, let $y\in\mathbb R^n$ and $r>0$, and write $\|f_j\|_n$ for the empirical norm of the $j$-th column of $X$. If $\hat\beta_L$ is any minimiser of the Lasso criterion (2.1),
--   $$
--   \frac1n\sum_{i=1}^n\big(y_i-(X\beta)_i\big)^2+2r\sum_{j=1}^M\|f_j\|_n|\beta_j| ,
--   $$
--   then $\hat\beta_L$ satisfies the Dantzig constraint (2.3):
--   $$
--   \Big|\frac1n\sum_{i=1}^nX_{ij}\big(y_i-(X\hat\beta_L)_i\big)\Big|\le r\,\|f_j\|_n\qquad(j=1,\dots,M),
--   $$
--   that is, $\big|\tfrac1nD^{-1/2}X^\top(y-X\hat\beta_L)\big|_\infty\le r$ with $D=\mathrm{diag}(\|f_j\|_n^2)$.
--
--   This is what makes the Lasso a feasible point of the Dantzig program, so that the Dantzig selector has $\ell_1$ norm at most that of any Lasso solution; the comparison of the two estimators starts from it.
--
--   **Formalization Note** The Lasso and the Dantzig constraint are those of the mission's definition file; the constraint is stated coordinatewise, which avoids $D^{-1/2}$ when a column norm vanishes (the paper's standing assumption $\|f_j\|_n\neq0$ is not needed here).
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 4, Eq. (2.3)

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

/-- (2.3): every Lasso solution satisfies the Dantzig constraint. -/
theorem eq_2_3_lasso_dantzig_feasible {n M : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (βL : Fin M → ℝ) (hL : IsLasso X y r βL) :
    DantzigFeasible X y r βL := by sorry

end LassoDantzig.Equivalence

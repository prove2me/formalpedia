-- Prove2me | Theorems.Thm_LassoDantzig_Lasso_eq_B6_kkt
-- name    : LassoDantzig.Lasso.eq_B6_kkt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:18:43.394389+00:00
-- url     : https://prove2.me/theorems/70c34c80-5be8-4ccf-b9aa-9c4e51b927e8
-- title:
--   Appendix B, (B.6) — optimality conditions of the Lasso
-- statement:
--   Let $n\ge1$, $X\in\mathbb R^{n\times M}$ with columns $x_{(1)},\dots,x_{(M)}$, $y\in\mathbb R^n$ and $r>0$. A vector $\hat\beta_L\in\mathbb R^M$ minimises $\frac1n|y-X\beta|_2^2+2r|\beta|_1$ (the Lasso (7.2)) if and only if, for every $j=1,\dots,M$,
--   $$
--   \frac1n x_{(j)}^\top(y-X\hat\beta_L)=r\,\mathrm{sign}(\hat\beta_{j,L})\quad\text{if }\hat\beta_{j,L}\ne0,
--   \qquad
--   \Big|\frac1n x_{(j)}^\top(y-X\hat\beta_L)\Big|\le r\quad\text{if }\hat\beta_{j,L}=0 .
--   $$
--
--   These conditions are used in the proof of Lemma B.1 to bound the number of non-zero coordinates of the Lasso solution, which yields the sparsity bound (7.9).
--
--   **Formalization Note** The paper writes (B.6) for the weighted Lasso (2.1) with right-hand sides $r\|f_j\|_n$; for the Lasso (7.2), whose weights are $1$ (the unit-diagonal case $\|f_j\|_n=1$), the right-hand sides are $r$, and the equivalence holds for every design $X$. $\mathrm{sign}$ is the real sign function.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 22, Appendix B, Eq. (B.6) (proof of Lemma B.1)

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- (B.6), p. 22, for the Lasso (7.2): for `r > 0`, `β̂` is a Lasso solution if and only if,
for every `j`, `(1/n) x_{(j)}ᵀ(y − Xβ̂) = r sign(β̂ⱼ)` when `β̂ⱼ ≠ 0` and
`|(1/n) x_{(j)}ᵀ(y − Xβ̂)| ≤ r` when `β̂ⱼ = 0`, where `x_{(j)}` is the `j`-th column of `X`. -/
theorem eq_B6_kkt {n M : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (βhat : Fin M → ℝ) :
    IsLasso X y r βhat ↔
      ∀ j : Fin M,
        (βhat j ≠ 0 →
          (1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i) = r * Real.sign (βhat j)) ∧
        (βhat j = 0 →
          |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i)| ≤ r) := by sorry

end LassoDantzig.Lasso

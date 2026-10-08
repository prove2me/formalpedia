-- Prove2me | Theorems.Thm_GassSaaty_ParametricPivot_lambdaBar_satisfies_ineq3_prime
-- name    : GassSaaty.ParametricPivot.lambdaBar_satisfies_ineq3_prime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:42:26.4942+00:00
-- url     : https://prove2.me/theorems/7cbeb6ab-141a-4bb6-8830-45458edab2ed
-- title:
--   Proof of the THEOREM, [1] — $\bar\lambda$ satisfies (3') for the new basis
-- statement:
--   Let $B$ be a basis, $\alpha_j, \beta_j$ its coefficients of $z_j - c_j = \alpha_j + \lambda\beta_j$, and suppose (Case A) that the inequalities (3), $\alpha_j + \lambda\beta_j \le 0$ for all $j$, are consistent. Let $s$ be an index with $\beta_s > 0$ attaining
--
--   $$
--   \bar\lambda = \min_{\beta_j > 0}\Big(-\frac{\alpha_j}{\beta_j}\Big) = -\frac{\alpha_s}{\beta_s}.
--   $$
--
--   Let $r = B(\ell)$ be a basic column with $y_{rs} > 0$, where $y_{rs}$ is the coefficient of $A_r$ in the expansion of $A_s$ in the basis, and let $B'$ be the basis obtained by bringing $A_s$ in and taking $A_r$ out. Write $\alpha'_j + \lambda\beta'_j$ for the quantities $z_j - c_j$ of $B'$. Then $\lambda = \bar\lambda$ satisfies
--
--   $$
--   \alpha'_j + \bar\lambda\,\beta'_j \le 0 \qquad (j = 1, \dots, n). \qquad (3')
--   $$
--
--   In the paper: at $\lambda = \bar\lambda$ the entering column has $z_s - c_s = \alpha_s + \bar\lambda\beta_s = 0$, and "by [1], the new basis will still be a minimum for $\lambda = \bar\lambda$, i.e., $\bar\lambda$ satisfies (3')". Combined with the optimality criterion this gives the first sentence of the THEOREM.
--
--   **Formalization Note** The conclusion is stated as the inequalities (3'), not as optimality; optimality at $\bar\lambda$ follows with the referenced optimality criterion and feasibility of the new basic solution. $\bar\lambda$ is written as the real number $-\alpha_s/\beta_s$ with $s$ attaining the minimum (finite case of (5)). The ratio test, feasibility and nondegeneracy are not needed for this step and are not assumed; only $y_{rs} > 0$ (`0 < pivotColumn A B s ℓ`), which makes $B'$ a basis. $r = B(\ell)$ is the column index of the leaving vector and $\ell$ its row.
-- source:
--   Gass and Saaty, The computational algorithm for the parametric objective function, Naval Res. Logist. Quart. 2 (1955), p. 41, proof of the THEOREM, Eq. (3') ("By [1], the new basis will still be a minimum for λ = λ̄")

import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem lambdaBar_satisfies_ineq3_prime {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hsmin : ∀ j, 0 < beta A d' B j →
      -alpha A d B s / beta A d' B s ≤ -alpha A d B j / beta A d' B j)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    ∀ j, alpha A d B' j + (-alpha A d B s / beta A d' B s) * beta A d' B' j ≤ 0 := by sorry

end GassSaaty.ParametricPivot

-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_matrix_pair_residual_bound_explicit
-- name    : HlawkaSchatten.DiagonalCutoff21.matrix_pair_residual_bound_explicit
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T08:28:21.823599+00:00
-- url     : https://prove2.me/theorems/801ebba3-077b-43ec-b4b4-cb2aa8f6fee4
-- title:
--   Six pair residuals controlled by the full matrix energy
-- statement:
--   Let $U$ be any real $3\times3$ matrix, let $\rho\ge0$, and let six real coefficients $\theta_{ki}$ satisfy $|\theta_{ki}|\le\rho$, indexed by $k,i\in\{0,1,2\}$ with $i\ne k$. If $\{j,r,k\}=\{0,1,2\}$, set $e_{ki}=U_{ji}+U_{ri}-\theta_{ki}(U_{jk}+U_{rk})$. Then
--
--   $$\sum_{k=0}^2\sum_{i\ne k}e_{ki}^2\le(7/4+2\rho)^2\sum_{j=0}^2\sum_{i=0}^2 U_{ji}^2.$$
--
--   This controls the non-radial error in the pair Hessian bound. It requires no orthogonality condition on $U$.
--
--   **Formalization Note** The six coefficients and residuals are ordered as $(k,i)=(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)$.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Section 6.2, equation (34), including the two operator estimates immediately preceding it.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

theorem HlawkaSchatten.DiagonalCutoff21.matrix_pair_residual_bound_explicit (U : Fin 3 → Fin 3 → ℝ)
    (theta : Fin 6 → ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    (htheta : ∀ i, |theta i| ≤ rho) :
    ∑ i, ((![U 1 1 + U 2 1, U 1 2 + U 2 2, U 0 0 + U 2 0, U 0 2 + U 2 2, U 0 0 + U 1 0, U 0 1 + U 1 1] : Fin 6 → ℝ) i - theta i * (![U 1 0 + U 2 0, U 1 0 + U 2 0, U 0 1 + U 2 1, U 0 1 + U 2 1, U 0 2 + U 1 2, U 0 2 + U 1 2] : Fin 6 → ℝ) i) ^ 2 ≤
      (7 / 4 + 2 * rho) ^ 2 * (∑ j, ∑ i, U j i ^ 2) := by sorry

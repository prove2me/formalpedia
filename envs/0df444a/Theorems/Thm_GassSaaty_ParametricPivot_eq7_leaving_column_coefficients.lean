-- Prove2me | Theorems.Thm_GassSaaty_ParametricPivot_eq7_leaving_column_coefficients
-- name    : GassSaaty.ParametricPivot.eq7_leaving_column_coefficients
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:42:28.922989+00:00
-- url     : https://prove2.me/theorems/8541e3e2-751c-493b-93eb-a54672ef92f4
-- title:
--   Eq. (7) — after the pivot, $\alpha'_r = -\alpha_s/y_{rs}$ and $\beta'_r = -\beta_s/y_{rs}$
-- statement:
--   Let $B$ be a basis, $s$ a column index and $r = B(\ell)$ a basic column with $y_{rs} > 0$, where $A_s = \sum_i y_{is} A_{B(i)}$. Let $B'$ be obtained from $B$ by replacing $A_r$ with $A_s$. Write $\alpha_j + \lambda\beta_j$ and $\alpha'_j + \lambda\beta'_j$ for the quantities $z_j - c_j$ of $B$ and $B'$ under the cost $d + \lambda d'$. Then the leaving column $r$ has, in the new basis,
--
--   $$
--   \alpha'_r = -\frac{\alpha_s}{y_{rs}}, \qquad \beta'_r = -\frac{\beta_s}{y_{rs}}. \qquad (7)
--   $$
--
--   These formulas are the step of the proof of the THEOREM that turns the sign of $z'_r - c'_r$ into the sign of $z_s - c_s$.
--
--   **Formalization Note** $y_{rs}$ is `pivotColumn A B s ℓ`, the $\ell$-th coordinate of $B^{-1}A_s$; the paper indexes it by the column $r$, Lean by the row $\ell$ with $B(\ell) = r$. Since $\alpha, \beta$ are minus the platform's reduced costs, (7) is equivalently $\bar c'_r = -\bar c_s / y_{rs}$ for both cost vectors. The hypothesis $y_{rs} > 0$ is the paper's (6); only $y_{rs} \neq 0$ is used.
-- source:
--   Gass and Saaty, The computational algorithm for the parametric objective function, Naval Res. Logist. Quart. 2 (1955), p. 41, proof of the THEOREM, Eq. (7) (with (6))

import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem eq7_leaving_column_coefficients {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (s : Fin n) (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    alpha A d B' (B ℓ) = -alpha A d B s / pivotColumn A B s ℓ ∧
      beta A d' B' (B ℓ) = -beta A d' B s / pivotColumn A B s ℓ := by sorry

end GassSaaty.ParametricPivot

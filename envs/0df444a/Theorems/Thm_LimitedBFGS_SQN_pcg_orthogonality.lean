-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_orthogonality
-- name    : LimitedBFGS.SQN.pcg_orthogonality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:27:34.239981+00:00
-- url     : https://prove2.me/theorems/fc88a0c1-646c-40c7-acf6-0636d6b98278
-- title:
--   Eq. (16), p. 777, index range corrected — PCG: $g_i^T H_0 g_j = 0$ ($i \ne j$) and $g_i^T d_j = 0$ ($j < i$)
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ with $A$ symmetric positive definite, let $H_0$ be symmetric positive definite, and let $x_0 \in \mathbb{R}^n$. Run the preconditioned conjugate gradient method with fixed preconditioner $H_0$ and exact line searches from $x_0$, with iterates $x_i$, directions $d_i$ and gradients $g_i = A x_i + b$. Then
--
--   $$g_i^T H_0 g_j = 0 \quad (i \neq j), \qquad g_i^T d_j = 0 \quad (j < i).$$
--
--   The gradients are mutually orthogonal in the inner product defined by $H_0$, and each gradient is orthogonal to all earlier search directions. The first relation is what forces termination: at most $n$ nonzero vectors can be mutually $H_0$-orthogonal in $\mathbb{R}^n$.
--
--   **Formalization Note** The printed (16) says "$g_i^T d_j = 0$ for $i \ne j$". For $i < j$ this is false in general: on random instances with $n = 7$, $|g_i^T d_j|$ for $i < j$ reaches values of order $10^2$ while the $j < i$ values vanish to rounding error. The paper's own use of it on p. 778, "(iii) $g_{m+3}^T d_i = 0$, $i = 0, \dots, m+2$", is the case $j < i$, which is what is stated here. The printed ranges $i \le m+2$, $j \le m+1$ belong to the SCG argument; for the PCG with fixed preconditioner the relations hold for all indices, including after the minimizer is reached (all later gradients and directions are $0$).
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777, eq. (16) (range 'i ≠ j' of the second relation corrected to j < i, as used on p. 778, (iii))

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Eq. (16), p. 777 (index range corrected): along the PCG with fixed preconditioner `H₀` on a
strictly convex quadratic with exact line searches, `g_iᵀ H₀ g_j = 0` for `i ≠ j` and
`g_iᵀ d_j = 0` for `j < i`. -/
theorem pcg_orthogonality {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    (∀ i j, i ≠ j →
        grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x) = 0) ∧
      (∀ i j, j < i → grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d = 0) := by sorry

end LimitedBFGS.SQN

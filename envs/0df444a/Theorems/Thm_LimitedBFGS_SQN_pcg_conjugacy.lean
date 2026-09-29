-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_conjugacy
-- name    : LimitedBFGS.SQN.pcg_conjugacy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:27:10.019032+00:00
-- url     : https://prove2.me/theorems/4da2b303-6498-4f40-b258-e0f53db57f1b
-- title:
--   Eq. (15), p. 777 — PCG with fixed preconditioner $H_0$: $d_i^T y_j = 0$ for $i \ne j$
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ with $A$ symmetric positive definite, let $H_0$ be symmetric positive definite, and let $x_0 \in \mathbb{R}^n$. Run the preconditioned conjugate gradient method with fixed preconditioner $H_0$ and exact line searches from $x_0$, producing iterates $x_i$, directions $d_i$ and gradients $g_i = Ax_i + b$, and put $y_j = g_{j+1} - g_j$. Then the directions are conjugate in the sense
--
--   $$d_i^T y_j = 0 \qquad \text{for all } i \neq j .$$
--
--   Since $y_j = \alpha_j A d_j$, this is the $A$-conjugacy of the search directions, the defining property of a conjugate gradient method.
--
--   **Formalization Note** The paper states (15) for $i, j = 0, 1, \dots, m+1$ within the argument for the SCG; for the PCG with fixed preconditioner it holds for all indices, and is stated so. After the iteration reaches the minimizer every later $d_i$ and $y_j$ is $0$, so the identity continues to hold. Indices are 0-based.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777, eq. (15)

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Eq. (15), p. 777: along the PCG with fixed preconditioner `H₀` on a strictly convex
quadratic with exact line searches, `d_iᵀ y_j = 0` for `i ≠ j`, where
`y_j = g_{j+1} − g_j`. -/
theorem pcg_conjugacy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) (i j : ℕ) (hij : i ≠ j) :
    (pcgIter A b H₀ x₀ i).d ⬝ᵥ
      (grad A b (pcgIter A b H₀ x₀ (j + 1)).x - grad A b (pcgIter A b H₀ x₀ j).x) = 0 := by sorry

end LimitedBFGS.SQN

-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_grad_orthogonality
-- name    : LimitedBFGS.SQN.pcg_grad_orthogonality
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T22:59:58.02151+00:00
-- url     : https://prove2.me/theorems/ed4c3170-ba85-40e0-8405-b02663008ed3
-- title:
--   Section 3, Eq. (16) first half, p. 777 — PCG with fixed preconditioner $H_0$: the gradients $g_i$ are pairwise $H_0$-orthogonal ($g_i^T H_0 g_j = 0$, $i \ne j$)
-- statement:
--   Let $A$ be symmetric positive definite, $H_0$ symmetric positive definite, and $x_0 \in \mathbb{R}^n$. Run the preconditioned conjugate gradient method with fixed preconditioner $H_0$ and exact line searches from $x_0$, writing $g_i = g(x_i) = A x_i + b$ for the gradient at the $i$-th iterate. Then the gradients are pairwise $H_0$-orthogonal:
--
--   $$g_i^\top H_0 g_j = 0 \qquad (i \ne j).$$
--
--   This is the first of the two conjugacy statements of Eq. (16), p. 777, restricted to the gradient family. It is the ingredient from which the quadratic termination of the PCG follows: the nonzero $g_i$ form a family of pairwise $H_0$-orthogonal nonzero vectors in $\mathbb{R}^n$, hence a linearly independent family, of which there can be at most $n$; so one of $g_0,\dots,g_{n-1}$ must vanish.
--
--   **Formalization Note** Indices are 0-based, and the statement quantifies over all $i, j : \mathbb{N}$ without restriction, so it also asserts that the orthogonality persists indefinitely, as in the printed (16). The companion half of (16), $g_i^\top d_j = 0$ for $j < i$, is the separate target `LimitedBFGS.SQN.pcg_orthogonality` and is deliberately not repeated here.
-- source:
--   Nocedal, Computing with the Limited-Storage BFGS Method, Section 3, p. 777, Eq. (16), and p. 778, "for quadratic functions and exact line searches the SCG is the same as the PCG with fixed preconditioner $H_0$ and has quadratic termination".

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Eq. (16), first half, p. 777: along the PCG with fixed preconditioner `H₀` on a strictly
convex quadratic with exact line searches, the gradients `gᵢ = grad A b xᵢ` are pairwise
`H₀`-orthogonal: `gᵢᵀ H₀ gⱼ = 0` whenever `i ≠ j`. -/
theorem pcg_grad_orthogonality {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∀ i j, i ≠ j →
      grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x) = 0 := by sorry

end LimitedBFGS.SQN

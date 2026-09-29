-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_step_coefficient
-- name    : LimitedBFGS.SQN.pcg_step_coefficient
-- status  : Open
-- author  : @WillR
-- created : 2026-09-27T23:30:33.843203+00:00
-- url     : https://prove2.me/theorems/d7ff0fcb-7b49-4eb8-8ed5-f96f02d15968
-- title:
--   Step-coefficient identity for the PCG with fixed preconditioner H0: the beta of (13) equals the H0-norm ratio
-- statement:
--   Let $f(x) = \tfrac12 x^TAx + b^Tx$ on $\mathbb{R}^n$ with $A$ symmetric positive definite, let $H_0$ be symmetric positive definite, and let $x_0 \in \mathbb{R}^n$. Run the preconditioned conjugate gradient method with fixed preconditioner $H_0$ and exact line searches from $x_0$, with iterates $x_m$, directions $d_m$ and gradients $g_m = A x_m + b$. Then
--
--   $$g_{m+1}^T d_m = 0 \qquad\text{and}\qquad \beta = \frac{g_{m+1}^T H_0 g_{m+1}}{g_m^T H_0 g_m}\quad\text{if } g_m^T H_0 g_m \neq 0,$$
--
--   where $\beta = \dfrac{y_m^T H_0 g_{m+1}}{y_m^T d_m}$ with $y_m = g_{m+1}-g_m$ is the coefficient in the direction recurrence $d_{m+1} = -H_0 g_{m+1} + \beta d_m$ of iteration (13) of the paper.
--
--   This is the classical conjugate-gradient step-coefficient identity, with the $H_0$-inner product in place of the Euclidean one. It is the ingredient that is neither a definition nor a direct induction, and it is what drives the orthogonality relations of eq. (15) ($d_i^Ty_j = 0$) and eq. (16) ($g_i^TH_0g_j = 0$ and $g_i^Td_j = 0$ for $j<i$) on p. 777.
--
--   **Formalization Note** The first relation is the exactness of the line search along $d_m$ and holds unconditionally. The second is stated for $g_m^T H_0 g_m \neq 0$ so that the ratio is defined; since $H_0$ is positive definite, $g_m \neq 0$ implies $g_m^T H_0 g_m > 0$, so the hypothesis is exactly the nondegeneracy of the ratio. The degenerate $g_m = 0$ case needs no separate treatment: once a gradient vanishes the iteration stops, all later gradients and directions are $0$, and the parent eq. (16) relations hold trivially from that index on.
--
--   The identity follows from two facts about the quadratic: the gradient difference along the search direction, $y_m = a_m A d_m$ with $a_m$ the exact line-search step, and the symmetry of $H_0$. The $H_0$-metric is essential; the corresponding Euclidean-metric norm identity is false for a preconditioner that does not commute with $A$.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777, iteration (13) and eqs. (15)-(16): the classical conjugate-gradient step-coefficient identity in the H0-inner product, with the exact line search along d_m

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Step-coefficient identity for the PCG with fixed preconditioner `H₀` (Nocedal 1980, p. 777,
iteration (13) with `H₀` in place of every `H_{i−1}`). Write `gm` for the gradient at
step `m` and `dm` for the direction there, and let `ym = gm1 - gm` be the gradient
difference along the search direction.

The coefficient `beta = ymᵀ H₀ gm1 / ymᵀ dm` defining the direction recurrence
`d_{m+1} = -H₀ g_{m+1} + beta d_m` is the ratio of successive squared `H₀`-norms
of the gradients,

    `beta = gm1ᵀ H₀ gm1 / gmᵀ H₀ gm`,

and, because the step along `dm` is an exact line search, the new gradient is orthogonal
to the direction just used,

    `gm1ᵀ dm = 0`.

This is the classical conjugate-gradient step-coefficient identity (with the `H₀`-inner
product in place of the Euclidean one) that drives the orthogonality relations of eq. (15)
and eq. (16); it is the ingredient that is neither a definition nor a direct induction.

The hypotheses are the positive definiteness of `A` and `H₀`, so that the line search is
well posed; the identity itself is a consequence of the exact line search and of the
symmetry of `H₀`. -/
theorem pcg_step_coefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ)
    (m : ℕ) :
    (let gm := grad A b (pcgIter A b H₀ x₀ m).x
     let dm := (pcgIter A b H₀ x₀ m).d
     let gm1 := grad A b (pcgIter A b H₀ x₀ (m + 1)).x
     let ym := gm1 - gm
     let beta := (ym ⬝ᵥ (H₀ *ᵥ gm1)) / (ym ⬝ᵥ dm)
     (gm1 ⬝ᵥ dm = 0) ∧
       ((gm ⬝ᵥ (H₀ *ᵥ gm)) ≠ 0 →
         beta = (gm1 ⬝ᵥ (H₀ *ᵥ gm1)) / (gm ⬝ᵥ (H₀ *ᵥ gm)))) := by sorry

end LimitedBFGS.SQN

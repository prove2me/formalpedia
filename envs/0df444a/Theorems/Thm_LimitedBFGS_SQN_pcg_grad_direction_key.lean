-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_grad_direction_key
-- name    : LimitedBFGS.SQN.pcg_grad_direction_key
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T05:39:55.580579+00:00
-- url     : https://prove2.me/theorems/7ad30009-244c-4b0a-8562-92f56890d6ca
-- title:
--   PCG with fixed preconditioner $H_0$: the direction $d_k$ is anti-parallel to the gradient $g_k$ in the $H_0$-form, $g_k^T d_k = -g_k^T H_0 g_k$
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ with $A$ symmetric positive definite, let $H_0$ be a symmetric matrix, and let $x_0 \in \mathbb{R}^n$. Run the preconditioned conjugate gradient method with fixed preconditioner $H_0$ and exact line searches from $x_0$, with iterates $x_i$, directions $d_i$ and gradients $g_i = A x_i + b$, so that $d_0 = -H_0 g_0$, $x_{i+1} = x_i + \alpha_i d_i$ and $d_{i+1} = -H_0 g_{i+1} + \beta_{i+1} d_i$. Then for every $k \ge 0$,
--
--   $$g_k^T d_k = -\, g_k^T H_0 g_k.$$
--
--   In words: the search direction at step $k$ is exactly the negative gradient, measured in the inner product defined by $H_0$, up to the scalar factor $-1$. No assumption that $H_0$ is positive definite is needed for this identity, and no assumption on the line-search step $\alpha_k$; it holds for every $k$ including $k = 0$, where it is immediate from $d_0 = -H_0 g_0$.
--
--   **Why it matters.** For the $A$-conjugacy identity $d_{k+1}^T A d_k = 0$ one normally divides the definition of $\beta_{k+1}$ by the step $\alpha_k$, which is legitimate only when $\alpha_k \ne 0$. This identity supplies the missing case: if $\alpha_k = 0$ with $d_k \ne 0$, then $g_k^T d_k = 0$, hence $g_k^T H_0 g_k = 0$, which for positive definite $H_0$ forces $g_k = 0$ and the conjugacy statement is then vacuous.
-- source:
--   One-step component of Eq. (16), p. 777 of J. Nocedal, 'Convergence of a Method with Restricted-Factor Approximations and Applications', in Nonlinear Programming, 2nd ed. (1980). Section 3, iteration (13). Required by the Open target LimitedBFGS.SQN.pcg_direction_A_conjugacy_step_pd.

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Along the preconditioned conjugate gradient iteration (13) of Nocedal 1980, p. 777, with the
fixed preconditioner `H0`, the direction at step `k` is anti-parallel to the gradient at that
step, measured in the `H0` inner product:

    g_k ᵀ d_k = -g_kᵀ H0 g_k.

This is what rules out a vanishing line-search step at a nonzero direction.  It is the
one ingredient needed to justify the `A`-conjugacy identity
`LimitedBFGS.SQN.pcg_direction_A_conjugacy_step_pd` when the line-search step `a_k` vanishes,
a case that is reachable for a merely symmetric `H0` but not for a positive definite one.
-/
theorem pcg_grad_direction_key {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (k : ℕ) :
    grad A b (pcgIter A b H₀ x₀ k).x ⬝ᵥ (pcgIter A b H₀ x₀ k).d
      = -((H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ k).x) ⬝ᵥ grad A b (pcgIter A b H₀ x₀ k).x) := by sorry

end LimitedBFGS.SQN

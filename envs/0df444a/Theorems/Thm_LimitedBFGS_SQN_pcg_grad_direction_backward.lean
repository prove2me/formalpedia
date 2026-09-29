-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_grad_direction_backward
-- name    : LimitedBFGS.SQN.pcg_grad_direction_backward
-- status  : Open
-- author  : @WillR
-- created : 2026-09-28T07:19:11.206263+00:00
-- url     : https://prove2.me/theorems/028353c0-b13d-42a3-b941-9375a6e41d7d
-- title:
--   Along the PCG with fixed preconditioner $H_0$, $g_i^T d_j = 0$ whenever $j < i$ (eq. (16), second half)
-- statement:
--   Along the preconditioned conjugate gradient method with a fixed positive definite preconditioner and exact line searches, the gradient at any iterate is orthogonal to every strictly earlier search direction.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777, iteration (13) and eq. (16) second half: gradient orthogonality to earlier search directions

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Along the preconditioned conjugate gradient iteration (13) of Nocedal 1980, p. 777, with the
fixed preconditioner `H0`, the gradient at a later iterate is orthogonal to every *strictly
earlier* search direction:

    g_i ᵀ d_j = 0    whenever    j < i,

where `g_k = grad A b (pcgIter A b H₀ x₀ k).x` and `d_k = (pcgIter A b H₀ x₀ k).d`.

**Proof.** The gradient of a quadratic is affine along a line, so the step from `x_k` with
length `a_k` along `d_k` moves the gradient by exactly

    g_{k+1} - g_k = a_k (A *ᵥ d_k),

and the one-step case `g_{k+1} ᵀ d_k = 0` is the defining property of the exact line search
(`exactStep_minimizes_grad`). For `j < k`, a strong induction on `i` now closes:

```lean
g_{k+1} ᵀ d_j = g_k ᵀ d_j + a_k (A *ᵥ d_k) ᵀ d_j
               = g_k ᵀ d_j   +  a_k d_j ᵀ (A *ᵥ d_k)
```

The first term is the hypothesis at the smaller index, and the second vanishes because the
search directions are `A`-conjugate, `d_j ᵀ (A *ᵥ d_k) = 0` for `j ≠ k`. Both ingredients are
independent of the gradient-orthogonality theorem `pcg_grad_orthogonality`.

**Ordering matters.** The identity holds only for `j < i`; it is *not* symmetric in the two
indices, and `g_j ᵀ d_i ≠ 0` in general for `j < i`. -/
theorem pcg_grad_direction_backward {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∀ i j : ℕ, j < i →
      grad A b (pcgIter A b H₀ x₀ i).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d = 0 := by sorry

end LimitedBFGS.SQN

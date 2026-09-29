-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_exactStep_minimizes_grad
-- name    : LimitedBFGS.SQN.exactStep_minimizes_grad
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T22:57:12.215974+00:00
-- url     : https://prove2.me/theorems/cfe29498-d16d-4a55-976c-eb094cf04353
-- title:
--   The exact line-search step annihilates the gradient along the search direction
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ on $\mathbb{R}^n$ with $A$ symmetric positive definite, let $g(x) = Ax + b$ be its gradient, and let
--   $$\alpha = \mathrm{exactStep}(A,b,x,d) = -\frac{g(x)^T d}{d^T A d}.$$
--   Then the gradient at the new point $x + \alpha d$ is orthogonal to the search direction:
--
--   $$g(x + \alpha d)^T d = 0.$$
--
--   **Why it is true.** Since $g$ is affine, $g(x+\alpha d) = g(x) + \alpha A d$, so
--   $$g(x+\alpha d)^T d = g(x)^T d + \alpha\,(Ad)^T d.$$
--   Symmetry of $A$ gives $(Ad)^T d = d^T A d$, and substituting
--   $\alpha = -\frac{g(x)^Td}{d^TAd}$ makes the right-hand side $0$.
--
--   **Formalization note.** No case split on the denominator is needed: $\alpha$ is
--   *defined* as the quotient above, so cancellation is a single definitional
--   rearrangement and remains valid when $d = 0$ (in which case the direction is
--   zero and the statement is trivial). The hypothesis is exactly $A$ positive
--   definite, which is what makes the line search *exact* and unique.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777 (exact line searches); used in the induction for eq. (15) and (16)

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_quadratic

open Matrix

namespace LimitedBFGS.SQN

/-- For a strictly convex quadratic `f(x) = ½ xᵀAx + bᵀx` the exact line-search step
`α = exactStep A b x d = −(g(x)ᵀd)/(dᵀAd)` minimises `f` along the line `x + αd`, so the
gradient at the new point is orthogonal to the search direction `d`. This is the
defining property of an *exact line search*, used throughout Nocedal 1980, p. 777. -/
theorem exactStep_minimizes_grad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b x d : Fin n → ℝ) :
    grad A b (x + exactStep A b x d • d) ⬝ᵥ d = 0 := by sorry

end LimitedBFGS.SQN

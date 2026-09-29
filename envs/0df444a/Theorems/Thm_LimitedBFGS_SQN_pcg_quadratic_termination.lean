-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_quadratic_termination
-- name    : LimitedBFGS.SQN.pcg_quadratic_termination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:28:19.080718+00:00
-- url     : https://prove2.me/theorems/dbeb8457-4659-4a63-8b16-9a47abd27bd5
-- title:
--   Section 3, p. 778 — the PCG with fixed preconditioner $H_0$ reaches the minimizer of a strictly convex quadratic in at most $n$ steps
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ on $\mathbb{R}^n$ with $A$ symmetric positive definite, let $H_0$ be symmetric positive definite, and let $x_0 \in \mathbb{R}^n$. Run the preconditioned conjugate gradient method with fixed preconditioner $H_0$ and exact line searches from $x_0$, producing iterates $x_0, x_1, \dots$. Then there is $k \le n$ with
--
--   $$A x_k + b = 0,$$
--
--   i.e. $x_k$ is the unique minimizer of $f$. This is the **quadratic termination** property of the PCG.
--
--   The paper says, on p. 778, that "for quadratic functions and exact line searches the SCG is the same as the PCG with fixed preconditioner $H_0$ and has quadratic termination". The quadratic termination asserted there is the one of the PCG with fixed preconditioner $H_0$, stated here; the SQN method inherits it through its identity with this PCG.
--
--   **Formalization Note** "Quadratic termination" is read as the standard property: the minimizer is reached after at most $n$ steps. Indices are 0-based, so $x_n$ is the iterate after $n$ steps.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 778, Section 3 ('the SCG is the same as the PCG with fixed preconditioner H_0 and has quadratic termination')

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Quadratic termination of the PCG with fixed preconditioner `H₀` (Section 3, p. 778): on a
strictly convex quadratic with exact line searches, some iterate `x_k` with `k ≤ n` has
`A x_k + b = 0`. -/
theorem pcg_quadratic_termination {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∃ k ≤ n, grad A b (pcgIter A b H₀ x₀ k).x = 0 := by sorry

end LimitedBFGS.SQN

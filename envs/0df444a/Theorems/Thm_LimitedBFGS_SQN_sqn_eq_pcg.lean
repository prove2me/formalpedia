-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_sqn_eq_pcg
-- name    : LimitedBFGS.SQN.sqn_eq_pcg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:28:55.153984+00:00
-- url     : https://prove2.me/theorems/30df0414-714e-4a3f-ba10-8783092e2646
-- title:
--   Section 3, p. 778 — on a quadratic with exact line searches, SQN is identical to the PCG with fixed preconditioner $H_0$
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ on $\mathbb{R}^n$ with $A$ symmetric positive definite, let $H_0$ be symmetric positive definite, let $m \ge 1$ be the number of stored corrections and let $x_0 \in \mathbb{R}^n$. Run from $x_0$, with exact line searches:
--
--   1. the SQN method (17): $d_i = -H_i g_i$, $x_{i+1} = x_i + \alpha_i d_i$, where $H_i$ is the special BFGS matrix (4)–(5) built from $H_0$ and the $\min(i,m)$ most recent pairs $(s_j, y_j)$;
--   2. the preconditioned conjugate gradient method with fixed preconditioner $H_0$: $d_0 = -H_0 g_0$, $d_{i+1} = -H_0 g_{i+1} + \beta_{i+1} d_i$ with $\beta_{i+1} = y_i^T H_0 g_{i+1} / y_i^T d_i$.
--
--   Then for every $i \ge 0$ the two methods produce the same iterate and the same search direction:
--
--   $$x_i^{\mathrm{SQN}} = x_i^{\mathrm{PCG}}, \qquad -H_i g_i^{\mathrm{SQN}} = d_i^{\mathrm{PCG}} .$$
--
--   The limited-storage BFGS matrix, although it forgets all but the last $m$ corrections, acts on the current gradient exactly as the conjugate gradient recurrence does.
--
--   **Formalization Note** The page states only that the algorithms are "identical"; the equality of iterates and of directions at every step is how that is read. Both runs are total: after the minimizer is reached both stay there with zero directions, so the identity is stated for all $i$. $m \ge 1$ is essential: with $m = 0$ the SQN matrix is always $H_0$ and SQN is preconditioned steepest descent.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 778, Section 3, after (17) ('this algorithm is also identical to the PCG with fixed preconditioner')

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_sqnIter
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Section 3, p. 778: on a strictly convex quadratic with exact line searches and `m ≥ 1`, the
SQN (17) is identical to the PCG with fixed preconditioner `H₀`: the iterates and the search
directions coincide at every step. -/
theorem sqn_eq_pcg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (m : ℕ) (hm : 1 ≤ m)
    (x₀ : Fin n → ℝ) (i : ℕ) :
    (sqnIter A b H₀ m x₀ i).x = (pcgIter A b H₀ x₀ i).x ∧
      sqnDir A b H₀ (sqnIter A b H₀ m x₀ i) = (pcgIter A b H₀ x₀ i).d := by sorry

end LimitedBFGS.SQN

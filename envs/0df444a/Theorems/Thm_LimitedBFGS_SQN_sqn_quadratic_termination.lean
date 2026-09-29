-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_sqn_quadratic_termination
-- name    : LimitedBFGS.SQN.sqn_quadratic_termination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:29:19.38421+00:00
-- url     : https://prove2.me/theorems/52ae7577-50df-4daa-9d6c-a66e060a6624
-- title:
--   Section 3, p. 778 — the SQN (limited-storage BFGS) method terminates on a strictly convex quadratic in at most $n$ steps
-- statement:
--   Let $f(x) = \tfrac12 x^T A x + b^T x$ be a strictly convex quadratic on $\mathbb{R}^n$ ($A$ symmetric positive definite), let $H_0$ be a symmetric positive definite matrix, let $m \ge 1$ be the number of stored correction pairs, and let $x_0 \in \mathbb{R}^n$. Run the SQN method (17) from $x_0$ with exact line searches:
--
--   $$d_i = -H_i g_i, \qquad x_{i+1} = x_i + \alpha_i d_i, \qquad H_{i+1} = F(s_i, y_i, H_i),$$
--
--   where $g_i = A x_i + b$, $\alpha_i$ minimizes $f(x_i + \alpha d_i)$, $s_i = x_{i+1} - x_i$, $y_i = g_{i+1} - g_i$, and $F$ is the special BFGS update (4)–(5), which rebuilds $H_{i+1}$ from $H_0$ and the $m$ most recent pairs. Then there is $k \le n$ with
--
--   $$A x_k + b = 0,$$
--
--   that is, $x_k$ is the minimizer of $f$: the SQN method has **quadratic termination**.
--
--   This is the paper's main theoretical claim about the SQN (L-BFGS) method, stated on p. 778 ("Hence, it has quadratic termination") and repeated in the Conclusion (p. 781): the limited-storage update preserves the quadratic termination property of BFGS and conjugate gradients, for every number $m \ge 1$ of stored corrections.
--
--   **Formalization Note** "Quadratic termination" is read as the standard property of the PCG with which the paper identifies SQN: the minimizer is reached in at most $n$ steps. Indices are 0-based. The SQN matrix is rebuilt from $H_0$ and the stored pairs at every step, as in (4)–(5), not obtained by one BFGS update of the previous matrix. There is no stopping rule; after the minimizer is reached the iteration stays there. $H_0$ need not be diagonal (the paper's "diagonal" on p. 774 is a storage convenience not used in Section 3).
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 778, Section 3, after (17) ('Hence, it has quadratic termination'); p. 781, Section 6 (Conclusion). DOI 10.1090/s0025-5718-1980-0572855-7

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_sqnIter

open Matrix

namespace LimitedBFGS.SQN

/-- Section 3, p. 778 ("Hence, it has quadratic termination"): the SQN method (17) with `m ≥ 1`
stored corrections, a positive definite initial matrix `H₀` and exact line searches, applied to
the strictly convex quadratic `f(x) = ½ xᵀAx + bᵀx` on `ℝⁿ`, reaches the minimizer, i.e. an
iterate with `A x_k + b = 0`, after at most `n` steps. -/
theorem sqn_quadratic_termination {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (m : ℕ) (hm : 1 ≤ m)
    (x₀ : Fin n → ℝ) :
    ∃ k ≤ n, grad A b (sqnIter A b H₀ m x₀ k).x = 0 := by sorry

end LimitedBFGS.SQN

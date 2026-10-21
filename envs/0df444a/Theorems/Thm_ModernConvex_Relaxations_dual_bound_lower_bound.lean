-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_dual_bound_lower_bound
-- name    : ModernConvex.Relaxations.dual_bound_lower_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:45.697986+00:00
-- url     : https://prove2.me/theorems/9b357e2b-bd7c-4448-a32e-7c3e85cb5a14
-- title:
--   Proposition 4.3.1 — the optimal value of (4.3.9) is a lower bound for the optimal value of (4.3.5)
-- statement:
--   Consider the quadratically constrained problem (4.3.5),
--   $$\min_{x\in\mathbb R^n}\ x^TA_0x + 2b_0^Tx + c_0 \quad\text{s.t.}\quad x^TA_ix + 2b_i^Tx + c_i = 0,\ i = 1,\dots,m,$$
--   with symmetric $A_0, \dots, A_m$, and the semidefinite program (4.3.9),
--   $$\max_{\zeta,\lambda}\left\{\zeta : \begin{pmatrix} c_0 + \sum_{i=1}^m \lambda_ic_i - \zeta & b_0^T + \sum_{i=1}^m \lambda_ib_i^T \\ b_0 + \sum_{i=1}^m \lambda_ib_i & A_0 + \sum_{i=1}^m \lambda_iA_i\end{pmatrix} \succeq 0\right\}.$$
--   Then the optimal value of (4.3.9) is a lower bound for the optimal value of (4.3.5):
--   $$\mathrm{Opt}(4.3.9) \le \mathrm{Opt}(4.3.5),$$
--   both optimal values being taken in $[-\infty, +\infty]$.
--
--   This is the weak-duality step of the Lagrangian relaxation of a quadratically constrained problem: every feasible pair $(\zeta, \lambda)$ certifies the lower bound $\zeta$.
--
--   **Formalization Note** The optimal values are a supremum and an infimum in `EReal` (definition `ModernConvex.Relaxations.ShorScheme`), so the statement also covers the cases where (4.3.5) is infeasible ($+\infty$), (4.3.9) is infeasible ($-\infty$), or either is unbounded. Symmetry of $A_0, \dots, A_m$ is the hypothesis `P.IsSymmetric`.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 163, Proposition 4.3.1 (problems (4.3.5), p. 161, and (4.3.9), p. 163)

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_ShorScheme

open Matrix

namespace ModernConvex.Relaxations

/-- Ben-Tal–Nemirovski, Proposition 4.3.1, p. 163: the optimal value of the semidefinite program
(4.3.9) is a lower bound for the optimal value of (4.3.5). Both optimal values are taken in
`[−∞, +∞]` (a supremum and an infimum in `EReal`), so the statement also covers infeasible and
unbounded instances. -/
theorem dual_bound_lower_bound {n m : ℕ} (P : QuadraticProblem n m) (hP : P.IsSymmetric) :
    P.dualBoundValue ≤ P.optimalValue := by sorry

end ModernConvex.Relaxations

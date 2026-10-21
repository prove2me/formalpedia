-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_shor_relaxation_lower_bound
-- name    : ModernConvex.Relaxations.shor_relaxation_lower_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:53.883016+00:00
-- url     : https://prove2.me/theorems/7602f5a0-c1e7-439e-9ea6-8cc6fcff2a57
-- title:
--   Proposition 4.3.2 — Shor's semidefinite relaxation (4.3.11) is a lower bound for (4.3.5)
-- statement:
--   Consider the quadratically constrained problem (4.3.5),
--   $$\min_{x\in\mathbb R^n}\ x^TA_0x + 2b_0^Tx + c_0 \quad\text{s.t.}\quad x^TA_ix + 2b_i^Tx + c_i = 0,\ i = 1,\dots,m,$$
--   with symmetric $A_0, \dots, A_m$, and put $\bar A_i = \begin{pmatrix} c_i & b_i^T \\ b_i & A_i\end{pmatrix}$, $i = 0, \dots, m$. Then the optimal value of the semidefinite program
--   $$(4.3.11)\qquad \min_X\big\{\operatorname{Tr}(\bar A_0X) : \operatorname{Tr}(\bar A_iX) = 0,\ i = 1,\dots,m;\ X \succeq 0;\ X_{11} = 1\big\}$$
--   over symmetric $(n+1)\times(n+1)$ matrices $X$ is a lower bound for the optimal value of (4.3.5):
--   $$\mathrm{Opt}(4.3.11) \le \mathrm{Opt}(4.3.5),$$
--   both optimal values being taken in $[-\infty, +\infty]$.
--
--   The relaxation replaces the nonconvex set of dyadic matrices $\binom{1}{x}\binom{1}{x}^T$ by the convex set of positive semidefinite matrices with northwestern entry $1$; this is Shor's relaxation scheme.
--
--   **Formalization Note** The optimal values are infima in `EReal` (definition `ModernConvex.Relaxations.ShorScheme`), covering infeasible and unbounded instances. $X$ is indexed by `Unit ⊕ Fin n` with $X_{11}$ the entry at `(Sum.inl (), Sum.inl ())`. The book prints the lifted matrices in (4.3.11) as "$A_i = \ldots$"; they are the $\bar A_i$ of the display above, as the formula itself shows.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 164, Proposition 4.3.2 (problems (4.3.5), p. 161, and (4.3.11), p. 164)

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_ShorScheme

open Matrix

namespace ModernConvex.Relaxations

/-- Ben-Tal–Nemirovski, Proposition 4.3.2, p. 164: the optimal value of the semidefinite program
(4.3.11) is a lower bound for the optimal value of (4.3.5). Both optimal values are infima in
`[−∞, +∞]` (`EReal`). -/
theorem shor_relaxation_lower_bound {n m : ℕ} (P : QuadraticProblem n m) (hP : P.IsSymmetric) :
    P.shorValue ≤ P.optimalValue := by sorry

end ModernConvex.Relaxations

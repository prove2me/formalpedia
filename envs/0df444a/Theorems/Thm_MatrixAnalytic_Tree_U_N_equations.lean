-- Prove2me | Theorems.Thm_MatrixAnalytic_Tree_U_N_equations
-- name    : MatrixAnalytic.Tree.U_N_equations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:05.092726+00:00
-- url     : https://prove2.me/theorems/0a2c6645-173c-40f9-866c-0ddabf5bdfde
-- title:
--   Eq. (14.6) — N = (−U)⁻¹ and U = C + Σ_i A_i N D_i (finitely many phases)
-- statement:
--   Let $Q$ be the irreducible generator of a tree process with finitely many phases and data $\boldsymbol a, \boldsymbol d, C, A_i, D_i$. Let $N$ be the matrix of expected times spent in the root node $s\{\cdot\}$ before the first visit to $\emptyset$, and $U$ the infinitesimal generator of the process in the local time of $s\{\cdot\}$ before the first passage to $\emptyset$. Then $N$ is finite, $-U$ is invertible, and
--
--   $$N = (-U)^{-1}, \qquad U = C + \sum_{1 \le i \le m} A_i N D_i .$$
--
--   The pair of equations is the basis of the computational procedure (14.7)–(14.9) for $U$ and $N$, and hence for the matrix-product form of the stationary distribution.
--
--   **Formalization Note** The inverse is stated as a two-sided inverse, $N(-U) = (-U)N = I$, together with the finiteness of every entry of $N$ (an expected time, defined in $[0, \infty]$ and then read as a real), so no junk inverse is involved. The statement is restricted to finitely many phases: the book writes it for its general $m$, but a matrix inverse of an infinite matrix is not determined by the two products alone and the finiteness of $N$ is not established on the page for $m = \infty$. No recurrence hypothesis is needed, and none is on the page.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 292, Eq. (14.6) (derived on p. 291)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal

namespace MatrixAnalytic.Tree

/-- Eq. (14.6), p. 292, for finitely many phases: the expected-time matrix `N` is finite and is
the inverse of `−U`, `U` the generator in the local time of the node `s{·}` before the first
passage to `∅`, and `U = C + Σ_i A_i N D_i`. -/
theorem U_N_equations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T) :
    (∀ i j : ι, matN T i j ≠ ⊤) ∧
      matNR T * (-Matrix.of (matU T)) = 1 ∧
      (-Matrix.of (matU T)) * matNR T = 1 ∧
      Matrix.of (matU T) =
        Matrix.of T.C + ∑ i : ι, Matrix.of (T.A i) * matNR T * Matrix.of (T.D i) := by sorry

end MatrixAnalytic.Tree

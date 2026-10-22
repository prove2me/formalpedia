-- Prove2me | Theorems.Thm_MatrixAnalytic_Tree_recurrent_Nd_one
-- name    : MatrixAnalytic.Tree.recurrent_Nd_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:07.651701+00:00
-- url     : https://prove2.me/theorems/445569a8-8237-4142-9f68-c09c353b58f2
-- title:
--   Lemma 14.3.4 (first statement) — recurrence implies Nd = 1
-- statement:
--   Let $Q$ be the irreducible generator of a tree process with data $\boldsymbol a, \boldsymbol d, C, A_i, D_i$, and let $N$ be the matrix of expected times spent in the root node $s\{\cdot\}$ before the first visit to the empty state. If the process is recurrent, then
--
--   $$N\boldsymbol d = \mathbf 1 .$$
--
--   In words, $N\boldsymbol d$ is the vector of probabilities, from the states of $s\{\cdot\}$, of reaching $\emptyset$ in finite time, and recurrence forces these to be one. The condition is necessary, not sufficient.
--
--   **Formalization Note** $N$ has entries in $[0, \infty]$ and $\boldsymbol d \ge 0$; the identity is $\sum_j N_{ij} d_j = 1$ for every phase $i$, a sum of nonnegative terms in $[0, \infty]$. Recurrence means every state is recurrent (the jump chain returns with probability one). Phases form an arbitrary countable type.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 292, Lemma 14.3.4 (first statement)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal

namespace MatrixAnalytic.Tree

/-- Lemma 14.3.4, first statement, p. 292: a necessary condition for the tree process to be
recurrent is that `N d = 1`. -/
theorem recurrent_Nd_one {ι : Type*} [Countable ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T)
    (hrec : IsRecurrentProcess (gen T)) :
    ∀ i : ι, ∑' j : ι, matN T i j * ENNReal.ofReal (T.d j) = 1 := by sorry

end MatrixAnalytic.Tree

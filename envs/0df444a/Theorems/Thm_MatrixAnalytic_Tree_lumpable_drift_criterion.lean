-- Prove2me | Theorems.Thm_MatrixAnalytic_Tree_lumpable_drift_criterion
-- name    : MatrixAnalytic.Tree.lumpable_drift_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:03.335059+00:00
-- url     : https://prove2.me/theorems/ba83df76-1619-4ba8-b026-fa79986938f3
-- title:
--   Lemma 14.3.5 — D_i = D for all i: positive recurrent iff αA1 < αD1
-- statement:
--   Let $Q$ be the irreducible generator of a tree process with finitely many phases and data $\boldsymbol a, \boldsymbol d, C, A_i, D_i$. Assume that $D_i = D$ independently of $i$, define $A = \sum_{1 \le i \le m} A_i$, assume that the generator $A + C + D$ is irreducible, and let $\alpha$ be the row vector with
--
--   $$\alpha(A + C + D) = \mathbf 0, \qquad \alpha\mathbf 1 = 1 .$$
--
--   Then the process is positive recurrent if and only if
--
--   $$\alpha A \mathbf 1 < \alpha D \mathbf 1 .$$
--
--   When all the $D_i$ coincide the tree process is lumpable to a quasi-birth-and-death process (stack size and top phase), and the lemma is the mean-drift criterion for that process.
--
--   **Formalization Note** The finiteness of the phase set and the irreducibility of $A + C + D$ are not written in the lemma; they are the hypotheses of the QBD drift criterion (Theorem 7.2.3) to which the book's proof reduces the lemma, and with them the vector $\alpha$ exists and is unique. The statement holds for every real $\alpha$ satisfying the two displayed equations. Positive recurrence is the return-time notion.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 293, Lemma 14.3.5

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal

namespace MatrixAnalytic.Tree

/-- Lemma 14.3.5, p. 293: assume `D_i = D` for every `i`, put `A = Σ_i A_i`, and let `α` be
such that `α(A + C + D) = 0`, `α1 = 1`. Then the tree process is positive recurrent if and only
if `αA1 < αD1`. The number of phases is finite and `A + C + D` is irreducible: these are the
hypotheses of the QBD drift criterion (Theorem 7.2.3) to which the book's proof reduces the
lemma. -/
theorem lumpable_drift_criterion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T)
    (D : ι → ι → ℝ) (hD : ∀ i : ι, T.D i = D)
    (hirr : IsIrreducibleGen (fun i j : ι => (∑ k : ι, T.A k i j) + T.C i j + D i j))
    (α : ι → ℝ)
    (hα : ∀ j : ι, ∑ i : ι, α i * ((∑ k : ι, T.A k i j) + T.C i j + D i j) = 0)
    (hα1 : ∑ i : ι, α i = 1) :
    IsPositiveRecurrentProcess (gen T) ↔
      ∑ i : ι, α i * ∑ j : ι, ∑ k : ι, T.A k i j < ∑ i : ι, α i * ∑ j : ι, D i j := by sorry

end MatrixAnalytic.Tree

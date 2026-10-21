-- Prove2me | Theorems.Thm_MatrixAnalytic_Tree_positive_recurrent_iff_sp_lt_one
-- name    : MatrixAnalytic.Tree.positive_recurrent_iff_sp_lt_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:06.941103+00:00
-- url     : https://prove2.me/theorems/19b72fd9-a8ed-4161-a237-cb121f06726c
-- title:
--   Lemma 14.3.4 (second statement) — m finite: positive recurrent iff sp(R) < 1
-- statement:
--   Let $Q$ be the irreducible generator of a tree process with finitely many phases and data $\boldsymbol a, \boldsymbol d, C, A_i, D_i$, let $N$ be its expected-time matrix and
--
--   $$R = \sum_{1 \le i \le m} A_i N .$$
--
--   Then the process is positive recurrent if and only if
--
--   $$\mathrm{sp}(R) < 1,$$
--
--   where $\mathrm{sp}$ denotes the spectral radius. This criterion reduces the stability question for the infinite tree to a spectral condition on one $m \times m$ matrix, although computing $R$ requires solving (14.6) first.
--
--   **Formalization Note** $R$ has entries in $[0, \infty]$; the right-hand side says that every entry of $R$ is finite and that the spectral radius of $R$, viewed as a complex matrix, is less than one. Positive recurrence is the return-time notion. Finding F2 (low confidence) notes that the book's one-line proof of the "if" direction does not show recurrence; the statement is kept as printed.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 292, Lemma 14.3.4 (second statement)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal

namespace MatrixAnalytic.Tree

/-- Lemma 14.3.4, second statement, p. 292: if `m` is finite, the tree process is positive
recurrent if and only if `sp(R) < 1`, `R = Σ_i A_i N`. The right side includes the finiteness of
the entries of `R`, which is what makes `R` a real matrix with a spectral radius. -/
theorem positive_recurrent_iff_sp_lt_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T) :
    IsPositiveRecurrentProcess (gen T) ↔
      (∀ i j : ι, matR T i j ≠ ⊤) ∧
        spectralRadius ℂ (Matrix.of fun i j : ι => (((matR T i j).toReal : ℝ) : ℂ)) < 1 := by sorry

end MatrixAnalytic.Tree

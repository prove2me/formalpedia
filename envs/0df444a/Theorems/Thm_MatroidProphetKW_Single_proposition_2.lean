-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_proposition_2
-- name    : MatroidProphetKW.Single.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:00.605482+00:00
-- url     : https://prove2.me/theorems/288f0c33-80b0-4cc0-baab-aaffaea180b5
-- title:
--   Proposition 2 — $\sum_{x_i\in V} [w'(R(A_{i-1})) - w'(R(A_{i-1}\cup\{x_i\}))] \le w'(R(A))$
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid on a finite ground set, $w' \ge 0$ a weight assignment, and $R(\cdot)$ the remainder map of §3.2. Let $x_1, \dots, x_n$ be an input order. For any disjoint sets $A$, $V$ such that $A \cup V \in \mathcal I$, writing $A_{i-1} = A \cap \{x_1, \dots, x_{i-1}\}$,
--   $$\sum_{x_i \in V} \Big[w'(R(A_{i-1})) - w'(R(A_{i-1} \cup \{x_i\}))\Big] \;\le\; w'(R(A)).$$
--
--   The inequality holds for every non-negative $w'$, not only in expectation. Taking expectations gives Property (3) of Definition 1 for the thresholds (9) with $\alpha = 2$.
--
--   **Formalization Note** The input order is an explicit list containing every element exactly once, and $A_{i-1}$ is the set of elements of $A$ that precede $x_i$ in it.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 8, Proposition 2

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Online

namespace MatroidProphetKW.Single

/-- Proposition 2 (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 8), pointwise in `w′ ≥ 0`: let
`x_1, …, x_n` be an input order `l`; for any disjoint sets `A`, `V` with `A ∪ V ∈ ℐ`, writing
`A_{i−1} = A ∩ {x_1, …, x_{i−1}}`,
  `∑_{x_i ∈ V} [w′(R(A_{i−1})) − w′(R(A_{i−1} ∪ {x_i}))] ≤ w′(R(A))`. -/
theorem proposition_2 {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) (w' : α → ℝ) (hw' : ∀ x, 0 ≤ w' x)
    (l : List α) (hl : IsOrder l) (A V : Finset α) (hdisj : Disjoint A V)
    (hAV : M.Indep (↑(A ∪ V) : Set α)) :
    ∑ x ∈ V, (wt w' (Rset M (A.filter (fun y => l.idxOf y < l.idxOf x)) w')
        - wt w' (Rset M (insert x (A.filter (fun y => l.idxOf y < l.idxOf x))) w'))
      ≤ wt w' (Rset M A w') := by sorry

end MatroidProphetKW.Single

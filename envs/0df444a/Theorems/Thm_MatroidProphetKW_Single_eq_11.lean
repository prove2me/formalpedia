-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_eq_11
-- name    : MatroidProphetKW.Single.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:45.790824+00:00
-- url     : https://prove2.me/theorems/d02c5197-8c70-408e-9fe7-6c0ff1bc0431
-- title:
--   (11) — marginal losses along the input order are at most those at $A$
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid on a finite ground set, $w' \ge 0$, and $R(\cdot)$ the remainder map of §3.2. Let $x_1, \dots, x_n$ be an input order and $A$, $V$ disjoint sets with $A \cup V \in \mathcal I$. For $x_i \in V$ write $A_{i-1} = A \cap \{x_1, \dots, x_{i-1}\}$. Then
--   $$\sum_{x_i \in V} \Big[w'(R(A_{i-1})) - w'(R(A_{i-1} \cup \{x_i\}))\Big] \;\le\; \sum_{x \in V} \Big[w'(R(A)) - w'(R(A \cup \{x\}))\Big]. \tag{11}$$
--
--   This is the first half of the proof of Proposition 2; it follows from Lemma 3 applied on subsets of $A \cup V$.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 8, (11) (proof of Proposition 2)

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Online

namespace MatroidProphetKW.Single

/-- Inequality (11) (Kleinberg–Weinberg, arXiv:1201.4764v1, proof of Proposition 2, p. 8): let
`x_1, …, x_n` be an input order `l`, let `A`, `V` be disjoint with `A ∪ V ∈ ℐ`, and for `x_i ∈ V`
let `A_{i−1} = A ∩ {x_1, …, x_{i−1}}`. Then
  `∑_{x_i ∈ V} [w′(R(A_{i−1})) − w′(R(A_{i−1} ∪ {x_i}))] ≤ ∑_{x ∈ V} [w′(R(A)) − w′(R(A ∪ {x}))]`. -/
theorem eq_11 {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) (w' : α → ℝ) (hw' : ∀ x, 0 ≤ w' x)
    (l : List α) (hl : IsOrder l) (A V : Finset α) (hdisj : Disjoint A V)
    (hAV : M.Indep (↑(A ∪ V) : Set α)) :
    ∑ x ∈ V, (wt w' (Rset M (A.filter (fun y => l.idxOf y < l.idxOf x)) w')
        - wt w' (Rset M (insert x (A.filter (fun y => l.idxOf y < l.idxOf x))) w'))
      ≤ ∑ x ∈ V, (wt w' (Rset M A w') - wt w' (Rset M (insert x A) w')) := by sorry

end MatroidProphetKW.Single

-- Prove2me | Theorems.Thm_MatroidProphetKW_Inter_proposition_2
-- name    : MatroidProphetKW.Inter.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:53.7904+00:00
-- url     : https://prove2.me/theorems/40cff614-ce61-452a-a973-745822ed36c3
-- title:
--   Proposition 2 for the matroid $\mathcal M_j$ — $\sum_{x_i\in V} [w'(R_j(A_{i-1})) - w'(R_j(A_{i-1}\cup\{x_i\}))] \le w'(R_j(A))$
-- statement:
--   Let $\mathcal I = \bigcap_{j} \mathcal I_j$ be an intersection of matroids on a finite ground set, let $w' \ge 0$ be a non-negative weight assignment, $B$ a maximum-$w'$-weight set in $\mathcal I$, and $R_j(\cdot)$ the remainders with respect to the $j$-th matroid. Fix an input order $x_1,\dots,x_n$ of the ground set and write $A_{i-1} = A \cap \{x_1,\dots,x_{i-1}\}$. For every $j$ and all disjoint sets $A, V$ with $A \cup V \in \mathcal I_j$,
--   $$\sum_{x_i \in V} \Big[ w'(R_j(A_{i-1})) - w'(R_j(A_{i-1} \cup \{x_i\})) \Big] \le w'(R_j(A)).$$
--
--   This is Proposition 2 of the paper applied to the single matroid $\mathcal M_j$, as §4.2 uses it ("the hypotheses of Proposition 2 are satisfied for all $j$"). It holds for every non-negative $w'$, not only in expectation. Summed over $j$ and integrated over $w'$, it gives property (14) for the thresholds of §4.2.
--
--   **Formalization Note** The hypothesis is $A \cup V \in \mathcal I_j$, which is implied by the paper's $A \cup V \in \mathcal I$. Here $B$ maximises $w'$ over the intersection $\mathcal I$, not over $\mathcal I_j$, so $R_j(A)$ is not in general a maximum-weight basis of $\mathcal M_j/A$ and Lemma 2 of the paper does not transfer verbatim; the inequality itself remains true.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 8, Proposition 2; applied per matroid on p. 10, §4.2 (proof of (14))

import Mathlib
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_Inter_Online

open MeasureTheory

namespace MatroidProphetKW.Inter

/-- Proposition 2 (p. 8), restated for the `j`-th matroid as used in §4.2 (p. 10): for an input
order `xs`, disjoint `A, V` with `A ∪ V ∈ ℐ_j`, and every non-negative `w′`,
`∑_{x_i ∈ V} [w′(R_j(A_{i-1})) − w′(R_j(A_{i-1} ∪ {x_i}))] ≤ w′(R_j(A))`, where
`A_{i-1} = A ∩ {x_1, …, x_{i-1}}`. -/
theorem proposition_2
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ}
    (M : Fin p → Matroid α) (hE : ∀ j, (M j).E = Set.univ) (j : Fin p)
    (xs : List α) (hnd : xs.Nodup) (hall : ∀ x, x ∈ xs)
    (A V : Finset α) (hAV : Disjoint A V) (hInd : (M j).Indep (↑(A ∪ V) : Set α))
    (w' : α → ℝ) (hw' : ∀ x, 0 ≤ w' x) :
    sumOn xs V (fun i =>
        MatroidProphetKW.Single.wt w' (Rj M j (A ∩ (xs.take i).toFinset) w') -
          MatroidProphetKW.Single.wt w' (Rj M j (insert xs[i] (A ∩ (xs.take i).toFinset)) w')) ≤
      MatroidProphetKW.Single.wt w' (Rj M j A w') := by sorry

end MatroidProphetKW.Inter

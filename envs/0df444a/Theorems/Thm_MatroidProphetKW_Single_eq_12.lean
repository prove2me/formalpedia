-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_eq_12
-- name    : MatroidProphetKW.Single.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:49.041445+00:00
-- url     : https://prove2.me/theorems/04333fc7-9ff1-42a4-a4cc-15175bde56a6
-- title:
--   (12) — $\sum_{x\in V} [w'(R(A)) - w'(R(A\cup\{x\}))] \le w'(R(A))$
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid on a finite ground set, $w' \ge 0$, and $R(\cdot)$ the remainder map of §3.2. For disjoint sets $A$, $V$ with $A \cup V \in \mathcal I$,
--   $$\sum_{x \in V} \Big[w'(R(A)) - w'(R(A \cup \{x\}))\Big] \;\le\; w'(R(A)). \tag{12}$$
--
--   This is the second half of the proof of Proposition 2: each marginal loss is bounded by the weight $w'(\phi(x))$ of the element of $R(A)$ exchanged for $x$ (Lemma 1 in $\mathcal M/A$), and distinct $x$ are exchanged for distinct elements.
--
--   **Formalization Note** The page ends (12) with $\sum_{x \in V} w'(\phi(x)) = w'(R)$, which is exact when $|V| = |R(A)|$, the case in which Lemma 1 applies. In general $|V| \le |R(A)|$ and $\phi$ maps $V$ injectively into $R(A)$, so the sum is at most $w'(R(A))$; the statement gives the endpoints of the chain, $\le w'(R(A))$.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 9, (12) (proof of Proposition 2)

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting

namespace MatroidProphetKW.Single

/-- Inequality (12) (Kleinberg–Weinberg, arXiv:1201.4764v1, proof of Proposition 2, p. 9): for
disjoint `A`, `V` with `A ∪ V ∈ ℐ`,
  `∑_{x ∈ V} [w′(R(A)) − w′(R(A ∪ {x}))] ≤ w′(R(A))`. -/
theorem eq_12 {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) (w' : α → ℝ) (hw' : ∀ x, 0 ≤ w' x)
    (A V : Finset α) (hdisj : Disjoint A V) (hAV : M.Indep (↑(A ∪ V) : Set α)) :
    ∑ x ∈ V, (wt w' (Rset M A w') - wt w' (Rset M (insert x A) w')) ≤ wt w' (Rset M A w') := by sorry

end MatroidProphetKW.Single

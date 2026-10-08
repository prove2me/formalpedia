-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_lemma_3
-- name    : MatroidProphetKW.Single.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:17.631987+00:00
-- url     : https://prove2.me/theorems/784ea45b-123b-4690-9891-62105eadbeaa
-- title:
--   Lemma 3 — $S \mapsto w'(R(S))$ is submodular on subsets of an independent set
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid on a finite ground set, $w' \ge 0$ a weight assignment, and $R(\cdot)$ the remainder map of §3.2 for $w'$. For any independent set $J$, the function $f(S) = w'(R(S))$ is a submodular set function on the subsets of $J$:
--   $$f(S \cup T) + f(S \cap T) \;\le\; f(S) + f(T) \qquad \text{for all } S, T \subseteq J.$$
--
--   Submodularity says the marginal loss $f(S) - f(S \cup \{x\})$ grows as $S$ grows; this is inequality (11) in the proof of Proposition 2.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 8, Lemma 3

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting

namespace MatroidProphetKW.Single

/-- Lemma 3 (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 8): for any independent set `J`, the
function `f(S) = w′(R(S))` is submodular on the subsets of `J`:
`f(S ∪ T) + f(S ∩ T) ≤ f(S) + f(T)` for all `S, T ⊆ J`. -/
theorem lemma_3 {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) (w' : α → ℝ) (hw' : ∀ x, 0 ≤ w' x)
    (J : Finset α) (hJ : M.Indep (↑J : Set α)) (S T : Finset α) (hS : S ⊆ J) (hT : T ⊆ J) :
    wt w' (Rset M (S ∪ T) w') + wt w' (Rset M (S ∩ T) w')
      ≤ wt w' (Rset M S w') + wt w' (Rset M T w') := by sorry

end MatroidProphetKW.Single

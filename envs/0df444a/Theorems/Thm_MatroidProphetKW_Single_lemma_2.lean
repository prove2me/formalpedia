-- Prove2me | Theorems.Thm_MatroidProphetKW_Single_lemma_2
-- name    : MatroidProphetKW.Single.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:46.791147+00:00
-- url     : https://prove2.me/theorems/e1fe3966-9ed6-4b76-8a77-f02cc9fe60a5
-- title:
--   Lemma 2 — $R(A)$ is a maximum-weight basis of the contraction $\mathcal M/A$
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid on a finite ground set, $w' \ge 0$ a weight assignment, and $R(\cdot)$ the remainder map of §3.2 for $w'$. For any independent set $A$, the set $R(A)$ is a maximum-weight basis of the contraction $\mathcal M/A$:
--   $$R(A) \text{ is a basis of } \mathcal M/A, \qquad w'(R(A)) \ge w'(B') \text{ for every basis } B' \text{ of } \mathcal M/A.$$
--
--   Lemma 2 identifies $w'(R(A))$ with the optimum of the contracted matroid, which makes it independent of how ties in the choice of $B$ are broken, and is the basis of Lemma 3.
--
--   **Formalization Note** The contraction is Mathlib's `M.contract A`, whose ground set is $\mathcal U - A$ (Definition 2, p. 7). The page says "the maximum weight basis"; with ties this means "a" maximum-weight basis, which is what the statement asserts.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 8, Lemma 2 (contraction: Definition 2, p. 7)

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting

namespace MatroidProphetKW.Single

/-- Lemma 2 (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 8): for any independent set `A`, the set
`R(A)` is a maximum-weight basis of the contraction `ℳ/A`: it is a basis of `ℳ/A`, and no basis of
`ℳ/A` has larger `w′`-weight. -/
theorem lemma_2 {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) (w' : α → ℝ) (hw' : ∀ x, 0 ≤ w' x)
    (A : Finset α) (hA : M.Indep (↑A : Set α)) :
    (M.contract (↑A : Set α)).IsBase (↑(Rset M A w') : Set α) ∧
      ∀ B' : Finset α, (M.contract (↑A : Set α)).IsBase (↑B' : Set α) →
        wt w' B' ≤ wt w' (Rset M A w') := by sorry

end MatroidProphetKW.Single

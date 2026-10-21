-- Prove2me | Theorems.Thm_IwataFF_SFM_lemma_4_1
-- name    : IwataFF.SFM.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:25.013463+00:00
-- url     : https://prove2.me/theorems/c10d161c-1ee0-499a-bbfb-305e00d50256
-- title:
--   Lemma 4.1 — at the end of the δ-scaling phase, $x(w) < -n^2\delta$ implies $w$ belongs to every minimizer
-- statement:
--   Let $V$ be a finite nonempty set with $|V| = n$ and $f$ a real submodular function on $V$ with $f(\emptyset) = 0$. Consider a state of the scaling algorithm satisfying the invariants and at the end of a $\delta$-scaling phase ($S = \emptyset$, or $T = \emptyset$, or $Z = \emptyset$ and $W \cap T = \emptyset$), with $x = \sum_i \lambda_i y_i$. If $w \in V$ satisfies
--   $$x(w) < -n^2\delta,$$
--   then $w$ belongs to every minimizer of $f$.
--
--   This proximity lemma is what lets the strongly polynomial algorithm fix elements without running the scaling algorithm to the end.
--
--   **Formalization Note** "End of the phase" is the prose end condition (see Lemma 3.3). The state is any state with the invariants.
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, p. 12, Lemma 4.1

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase

namespace IwataFF.SFM

/-- Lemma 4.1 (arXiv:math/0004089v1, p. 12): at the end of the δ-scaling phase, if
`x(w) < −n²δ`, then `w` belongs to every minimizer of `f`. -/
theorem lemma_4_1 {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hinv : PhaseInv V st) (hend : PhaseEnd f V st)
    (w : α) (hw : w ∈ V) (hxw : xOf f st w < -((V.card : ℝ) ^ 2) * st.delta) :
    ∀ X : Finset α, IsMinimizer V f X → w ∈ X := by sorry

end IwataFF.SFM

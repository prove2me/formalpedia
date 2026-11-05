-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_weakRightAverageOrbit_subset_ball
-- name    : OAI.BoundedHochschild.KadisonRingrose.weakRightAverageOrbit_subset_ball
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:43:09.893977+00:00
-- url     : https://prove2.me/theorems/cfefffe5-f58c-4d8b-bc98-b5e482fc3838
-- title:
--   The weak right-averaging orbit stays in the ball of the complete bound
-- statement:
--   Let $N$ be a unital C*-algebra with star-ordered partial order and predual $X$ via an isometric conjugate-linear isomorphism $e:X^*\to N$, with no finite central summand: a central projection whose corner is finite vanishes (`NoFiniteCentralSummand`). Let $T:N\to N$ be a bounded linear map with complete bound $C$. Then the closure of the right averages $a\mapsto\sum_iT(am_i)m_i^*$, $\sum_im_im_i^*=1$, viewed as maps into $X^*$ with the weak-* topology (`weakRightAverageOrbit`), lies in the ball of radius $C$:
--
--   $$\text{every }F\text{ in the orbit is additive, conjugate-homogeneous, and }\|F(a)\|\le C\|a\|\quad(\texttt{weakOperatorBall }C).$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.weakRightAverageOrbit_subset_ball`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/RightAveragingOrbit.lean#L77

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

universe u
variable {N X : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem weakRightAverageOrbit_subset_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (hno : NoFiniteCentralSummand N) (T : N →L[ℂ] N) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) : weakRightAverageOrbit e T ⊆ weakOperatorBall C := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI

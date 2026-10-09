-- Prove2me | Theorems.Thm_ModernOnlineLearning_Reductions_lemma_12_2_subdiff
-- name    : ModernOnlineLearning.Reductions.lemma_12_2_subdiff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:07.899795+00:00
-- url     : https://prove2.me/theorems/c5e37dfe-103e-44f6-aeea-ee8d5566685c
-- title:
--   Lemma 12.2, fourth claim — subdifferential outside the set
-- statement:
--   Let $V$ be nonempty, closed, and convex. If $x\notin V$ and $y\in\Pi_V(x)$, then a continuous linear functional $g$ is a full-space subgradient of $d_V$ at $x$ exactly when
--   $$\|g\|_*=1,\qquad g(x-y)=\|x-y\|,\qquad g(u-y)\le0\quad\text{for every }u\in V.$$
--   This characterizes the distance subgradients used by the linear surrogate choices.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 12.2, fourth claim, p. 193

import Mathlib
import Definitions.Def_ModernOnlineLearning_Reductions_Setting

namespace ModernOnlineLearning.Reductions

/-- Orabona, Lemma 12.2, fourth claim, p. 193. -/
theorem lemma_12_2_subdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V)
    (x y : E) (hx : x ∉ V) (hy : IsProjection V x y) :
    ∀ g : E →L[ℝ] ℝ,
      IsSubgradient (distance V) x g ↔
        ‖g‖ = 1 ∧ g (x - y) = ‖x - y‖ ∧ ∀ u ∈ V, g (u - y) ≤ 0 := by sorry

end ModernOnlineLearning.Reductions

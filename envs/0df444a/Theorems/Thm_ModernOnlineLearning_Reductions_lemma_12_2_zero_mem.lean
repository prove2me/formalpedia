-- Prove2me | Theorems.Thm_ModernOnlineLearning_Reductions_lemma_12_2_zero_mem
-- name    : ModernOnlineLearning.Reductions.lemma_12_2_zero_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:06.901976+00:00
-- url     : https://prove2.me/theorems/38aa49a8-8627-47b1-b278-b2fab445b69d
-- title:
--   Lemma 12.2, third claim — zero subgradient at a feasible point
-- statement:
--   Let $V$ be a nonempty closed convex set and let $x\in V$. Then the zero functional belongs to the full-space subdifferential of the distance function:
--   $$0\in\partial d_V(x).$$
--   This covers the case where the unconstrained learner already predicts a feasible point.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 12.2, third claim, p. 193

import Mathlib
import Definitions.Def_ModernOnlineLearning_Reductions_Setting

namespace ModernOnlineLearning.Reductions

/-- Orabona, Lemma 12.2, third claim, p. 193. -/
theorem lemma_12_2_zero_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) (x : E) (hx : x ∈ V) :
    IsSubgradient (distance V) x (0 : E →L[ℝ] ℝ) := by sorry

end ModernOnlineLearning.Reductions

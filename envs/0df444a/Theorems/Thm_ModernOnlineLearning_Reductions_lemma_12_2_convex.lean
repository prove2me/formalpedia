-- Prove2me | Theorems.Thm_ModernOnlineLearning_Reductions_lemma_12_2_convex
-- name    : ModernOnlineLearning.Reductions.lemma_12_2_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:46.069989+00:00
-- url     : https://prove2.me/theorems/91cc7c09-de1a-4d4e-a854-d909b7fbdd59
-- title:
--   Lemma 12.2, first claim — distance to a convex set is convex
-- statement:
--   Let $V$ be a nonempty closed convex set in a finite-dimensional real normed space, and let $d_V(x)$ be the distance from $x$ to $V$. Then
--   $$d_V(\lambda x+(1-\lambda)y)\le\lambda d_V(x)+(1-\lambda)d_V(y)\quad(0\le\lambda\le1).$$
--   This establishes convexity of the distance term in the surrogate losses of Theorem 12.5.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 12.2, first claim, p. 193

import Mathlib
import Definitions.Def_ModernOnlineLearning_Reductions_Setting

namespace ModernOnlineLearning.Reductions

/-- Orabona, Lemma 12.2, first claim, p. 193. -/
theorem lemma_12_2_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) :
    ConvexOn ℝ Set.univ (distance V) := by sorry

end ModernOnlineLearning.Reductions

-- Prove2me | Theorems.Thm_ModernOnlineLearning_Reductions_lemma_12_2_lipschitz
-- name    : ModernOnlineLearning.Reductions.lemma_12_2_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:13.72621+00:00
-- url     : https://prove2.me/theorems/d9c0e506-78b5-4ec6-8513-4401c7064127
-- title:
--   Lemma 12.2, second claim — distance is 1-Lipschitz
-- statement:
--   Let $V$ be a nonempty closed convex set in a finite-dimensional real normed space. Its distance function satisfies
--   $$|d_V(x)-d_V(y)|\le\|x-y\|\qquad\text{for all }x,y.$$
--   This controls the dual norm of every subgradient of the distance function and therefore the surrogate gradients.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 12.2, second claim, p. 193

import Mathlib
import Definitions.Def_ModernOnlineLearning_Reductions_Setting

namespace ModernOnlineLearning.Reductions

/-- Orabona, Lemma 12.2, second claim, p. 193. -/
theorem lemma_12_2_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) :
    LipschitzWith 1 (distance V) := by sorry

end ModernOnlineLearning.Reductions

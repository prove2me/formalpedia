-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_RandomGrid_circle_norm_le_of_floor_ne
-- name    : OAI.EntropyRateDimension.RandomGrid.circle_norm_le_of_floor_ne
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:18:31.590009+00:00
-- url     : https://prove2.me/theorems/d8c94763-17c9-44c7-990e-506f91727c9b
-- title:
--   Points in different unit cells are close to an integer
-- statement:
--   Let $x,y$ be real numbers with $\lfloor x\rfloor\ne\lfloor y\rfloor$. Then the distance from $x$ to the nearest integer, which is the norm of $x$ in the circle $\mathbb R/\mathbb Z$, is at most $|y-x|$:
--   $$
--   \|x\|_{\mathbb R/\mathbb Z}\le|y-x| .
--   $$
--
--   So if a segment crosses a grid point, both of its endpoints are within its length of that point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean#L109-L129

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.RandomGrid
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] OAI.EntropyRateDimension.RandomGrid.unitCircleProbability

theorem OAI.EntropyRateDimension.RandomGrid.circle_norm_le_of_floor_ne {x y : ℝ} (h : ⌊x⌋ ≠ ⌊y⌋) :
    ‖(x : AddCircle (1 : ℝ))‖ ≤ |y - x| := by sorry

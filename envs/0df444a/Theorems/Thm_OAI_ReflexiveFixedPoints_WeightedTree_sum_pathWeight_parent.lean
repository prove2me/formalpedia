-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_WeightedTree_sum_pathWeight_parent
-- name    : OAI.ReflexiveFixedPoints.WeightedTree.sum_pathWeight_parent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:05:46.573645+00:00
-- url     : https://prove2.me/theorems/0c4a5ddb-a847-48a7-aba2-f8ad46db592c
-- title:
--   Summing path weights over children
-- statement:
--   In an ordered tree with positive edge weights summing to $1$ over the children of each parent, let $\pi_k$ be the path weights. For every function $f$ on level $k$,
--   $$
--   \sum_{c\text{ at level }k+1}\pi_{k+1}(c)\,f(\mathrm{par}\,c)=\sum_{p\text{ at level }k}\pi_k(p)\,f(p) .
--   $$
--
--   Path weights are a consistent family of probability measures on the levels.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/WeightedTree.lean#L96-L110

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedTree

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.WeightedTree
open scoped BigOperators
variable {T : OrderedTree} (W : WeightedTree T)

theorem OAI.ReflexiveFixedPoints.WeightedTree.sum_pathWeight_parent (k : ℕ) (f : T.Node k → ℝ) :
    (∑ c, W.pathWeight (k + 1) c * f (T.parent k c)) =
      ∑ p, W.pathWeight k p * f p := by sorry

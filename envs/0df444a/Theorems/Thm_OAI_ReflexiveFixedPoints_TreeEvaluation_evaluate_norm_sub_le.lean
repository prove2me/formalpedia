-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_evaluate_norm_sub_le
-- name    : OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_norm_sub_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:07:04.922056+00:00
-- url     : https://prove2.me/theorems/5c0901c5-fce2-44cd-82c8-5624714d240b
-- title:
--   Tree evaluation is Lipschitz in the path-weighted norm
-- statement:
--   Let $K$ be a convex subset of a real normed space and consider an ordered tree with positive edge weights $w(c)$ summing to $1$ over each parent's children, path weights $\pi_k(v)$, and nonexpansive node maps $f_{k,v}:K\to K$. The tree is evaluated bottom-up: for values $H$ at level $k+1$, $\mathrm{collapse}(H)(p)=f_{k,p}\bigl(\sum_{\mathrm{par}(c)=p}w(c)H(c)\bigr)$, and $\mathrm{ev}_k(H)$ iterates collapse up to the root. For two cutoff assignments $H,H'$ at level $k$,
--   $$
--   \|\mathrm{ev}_k(H)-\mathrm{ev}_k(H')\|\le\sum_v\pi_k(v)\,\|H(v)-H'(v)\| .
--   $$
--
--   Changing a single leaf moves the root by at most its path weight times the change.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/TreeEvaluation.lean#L118-L154

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeEvaluation

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

theorem OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_norm_sub_le (k : ℕ) (H H' : T.Node k → K) :
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤
      ∑ v, W.pathWeight k v * ‖(H v : X) - H' v‖ := by sorry

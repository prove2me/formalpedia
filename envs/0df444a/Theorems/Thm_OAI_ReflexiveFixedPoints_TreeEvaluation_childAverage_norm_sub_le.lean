-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_childAverage_norm_sub_le
-- name    : OAI.ReflexiveFixedPoints.TreeEvaluation.childAverage_norm_sub_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:06:22.15275+00:00
-- url     : https://prove2.me/theorems/7283d030-da7d-47a9-9018-d08fff0c9c32
-- title:
--   Child averages are weighted-contractive
-- statement:
--   Let $K$ be a convex subset of a real normed space and consider an ordered tree with positive edge weights $w(c)$ summing to $1$ over each parent's children, path weights $\pi_k(v)$, and nonexpansive node maps $f_{k,v}:K\to K$. The tree is evaluated bottom-up: for values $H$ at level $k+1$, $\mathrm{collapse}(H)(p)=f_{k,p}\bigl(\sum_{\mathrm{par}(c)=p}w(c)H(c)\bigr)$, and $\mathrm{ev}_k(H)$ iterates collapse up to the root. For two assignments $H,H'$ at level $k+1$ and a parent $p$,
--   $$
--   \Bigl\|\sum_{\mathrm{par}(c)=p}w(c)H(c)-\sum_{\mathrm{par}(c)=p}w(c)H'(c)\Bigr\|\le\sum_{\mathrm{par}(c)=p}w(c)\,\|H(c)-H'(c)\| .
--   $$
--
--   The averaging step never amplifies differences.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/TreeEvaluation.lean#L86-L103

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

theorem OAI.ReflexiveFixedPoints.TreeEvaluation.childAverage_norm_sub_le (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) :
    ‖(E.childAverage k H p : X) - E.childAverage k H' p‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - H' c‖ := by sorry

-- Prove2me | Theorems.Thm_OAI_IndependentProducts_pathEdges_parent
-- name    : OAI.IndependentProducts.pathEdges_parent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:32:46.497779+00:00
-- url     : https://prove2.me/theorems/0e4a1ca4-07ae-4edd-9ae5-d4e1f8bbbd71
-- title:
--   Path edges of a vertex are those of its parent plus the vertex itself
-- statement:
--   Let $\mathcal V$ be the set of finite sequences of positive integers, viewed as a rooted tree with root $\varnothing$, and let $\mathcal E=\mathcal V\setminus\{\varnothing\}$. For a nonroot vertex $e=(e_1,\dots,e_n)$ let $e^-=(e_1,\dots,e_{n-1})$ be its parent, and for $v=(v_1,\dots,v_m)\in\mathcal V$ let $E(v)=\{(v_1,\dots,v_j):1\le j\le m\}\subseteq\mathcal E$ be the set of path edges of $v$.
--
--   **Theorem.** For every nonroot vertex $e\in\mathcal E$,
--
--   $$
--   E(e)=\{e\}\cup E(e^-).
--   $$
--
--   The path to a vertex is the path to its parent followed by one more edge. Together with $e\notin E(e^-)$, this gives the recursion $\Pi_e(\omega)=\Pi_{e^-}(\omega)\,\omega(e)$ for the path products $\Pi_v(\omega)=\prod_{d\in E(v)}\omega(d)$, and it is the basic step for splitting a path product at a vertex on the path.
--
--   **Formalization Note** The statement is `pathEdges e.val = insert e (pathEdges e.val.dropLast)`, an equality of finite sets of edges.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/FiniteHeads.lean#L138-L154

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uκ

theorem OAI.IndependentProducts.pathEdges_parent (e : Edge) : pathEdges e.val = insert e (pathEdges e.val.dropLast) := by sorry

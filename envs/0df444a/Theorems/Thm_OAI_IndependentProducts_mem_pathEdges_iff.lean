-- Prove2me | Theorems.Thm_OAI_IndependentProducts_mem_pathEdges_iff
-- name    : OAI.IndependentProducts.mem_pathEdges_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:32:08.69104+00:00
-- url     : https://prove2.me/theorems/dcaf772f-69b7-439a-83eb-a1a4d26bb618
-- title:
--   Path edges of a vertex are exactly its nonempty prefixes
-- statement:
--   Let $\mathcal V$ be the set of finite sequences of positive integers (the vertices of a rooted tree with root $\varnothing$), let $\mathcal E=\mathcal V\setminus\{\varnothing\}$ be the set of nonroot vertices, and write $u\preceq v$ when $u$ is a prefix of $v$. For $v=(v_1,\dots,v_n)\in\mathcal V$ define its set of path edges
--   $$
--   E(v)=\big\{(v_1,\dots,v_j):\ 1\le j\le n\big\}\subseteq\mathcal E,
--   $$
--   the truncations of $v$ of positive length; these index the coordinates multiplied in the path product $\Pi_v(\omega)=\prod_{d\in E(v)}\omega(d)$.
--
--   **Theorem.** For every $v\in\mathcal V$ and every $e\in\mathcal E$,
--
--   $$
--   e\in E(v)\iff e\preceq v.
--   $$
--
--   The lemma translates membership in the finite index set of a path product into the prefix order of the tree; it is the basic tool for splitting path products at intermediate vertices and for comparing paths along different branches.
--
--   **Formalization Note** `pathEdges v` is the image of `Fin v.length` under the map sending $j$ to `v.take (j + 1)`, and edges are the nonempty lists.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/FiniteHeads.lean#L118-L129

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

theorem OAI.IndependentProducts.mem_pathEdges_iff (v : Vertex) (e : Edge) : e ∈ pathEdges v ↔ e.val <+: v := by sorry

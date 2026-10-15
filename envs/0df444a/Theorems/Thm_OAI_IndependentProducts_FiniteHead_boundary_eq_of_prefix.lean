-- Prove2me | Theorems.Thm_OAI_IndependentProducts_FiniteHead_boundary_eq_of_prefix
-- name    : OAI.IndependentProducts.FiniteHead.boundary_eq_of_prefix
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:29:54.479365+00:00
-- url     : https://prove2.me/theorems/886c0756-b8ea-476e-8e17-6bafe87501ea
-- title:
--   Boundary vertices of a finite head form an antichain
-- statement:
--   Let $\mathcal V$ be the set of finite sequences of positive integers, viewed as a rooted tree with root the empty sequence $\varnothing$. Write $u\preceq v$ if $u$ is a prefix of $v$, and for a nonroot vertex $v=(v_1,\dots,v_n)$ let $v^-=(v_1,\dots,v_{n-1})$ be its parent. A finite head is a finite set $T\subseteq\mathcal V$ that contains $\varnothing$ and is closed under prefixes ($u\preceq v$ and $v\in T$ imply $u\in T$). Its boundary is the set of first-exit vertices
--   $$
--   \partial T=\{e\in\mathcal V: e\ne\varnothing,\ e\notin T,\ e^-\in T\}.
--   $$
--
--   **Theorem.** For all $e,f\in\partial T$,
--
--   $$
--   e\preceq f\ \Longrightarrow\ e=f.
--   $$
--
--   Thus the boundary of a finite head is an antichain for the prefix order: no boundary vertex lies strictly below another. Consequently every vertex has at most one boundary vertex among its prefixes, and the subtrees hanging below distinct boundary vertices are disjoint, which is what allows the coordinates below different exit vertices to be resampled independently.
--
--   **Formalization Note** Vertices are `List ℕ+`, the prefix relation is `<+:`, the parent is `List.dropLast`, and `T.Boundary` is a subtype of the type of nonempty lists; the conclusion is equality in that subtype.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/FiniteHeads.lean#L25-L36

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

open OAI OAI.IndependentProducts OAI.IndependentProducts.FiniteHead
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uκ
variable (T : FiniteHead)

theorem OAI.IndependentProducts.FiniteHead.boundary_eq_of_prefix {e f : T.Boundary} (h : e.val.val <+: f.val.val) : e = f := by sorry

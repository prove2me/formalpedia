-- Prove2me | Theorems.Thm_OAI_IndependentProducts_pathProduct_child
-- name    : OAI.IndependentProducts.pathProduct_child
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:00:26.457986+00:00
-- url     : https://prove2.me/theorems/e809eaf5-133f-4a77-a98f-d54017e28c10
-- title:
--   The path product at a child is the parent's path product times the new coordinate
-- statement:
--   Let $\mathcal V$ be the tree of finite sequences of positive integers, $\mathcal E=\mathcal V\setminus\{\varnothing\}$ its set of nonroot vertices, and $\omega=(\omega_d)_{d\in\mathcal E}\in\mathbb{R}^{\mathcal E}$ a sample assigning a real number to every nonroot vertex. The path product of $v=(v_1,\dots,v_m)\in\mathcal V$ is
--
--   $$\Pi_v(\omega)=\prod_{j=1}^{m}\omega_{(v_1,\dots,v_j)},$$
--
--   the product of the sample values at the nonempty prefixes of $v$ (so $\Pi_\varnothing=1$). For $n\in\mathbb{N}$ let $\mathrm{ch}_n(v)=(v_1,\dots,v_m,n+1)$ be the $(n+1)$-st child of $v$, regarded also as a nonroot vertex.
--
--   For every vertex $v$, every $n\in\mathbb{N}$ and every sample $\omega$,
--
--   $$\Pi_{\mathrm{ch}_n(v)}(\omega)=\Pi_v(\omega)\,\omega_{\mathrm{ch}_n(v)} .$$
--
--   This multiplicative recursion is the basic identity of the independent-products construction: passing from a vertex to a child multiplies the path product by exactly one fresh coordinate. Together with independence of distinct coordinates it determines the size and the asymptotic behaviour of the child increments $\Pi_{\mathrm{ch}_n(v)}-\Pi_v=\Pi_v\,(\omega_{\mathrm{ch}_n(v)}-1)$.
--
--   **Formalization Note** In Lean the child is `child v n`, the list `v ++ [n+1]`, and the same vertex as an element of the edge type is `childEdge v n`. The identity holds pointwise for every sample; no measure is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/PathMoments.lean#L180-L199

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι

theorem OAI.IndependentProducts.pathProduct_child (v : Vertex) (n : ℕ) (ω : Sample) :
    pathProduct (child v n) ω = pathProduct v ω * ω (childEdge v n) := by sorry

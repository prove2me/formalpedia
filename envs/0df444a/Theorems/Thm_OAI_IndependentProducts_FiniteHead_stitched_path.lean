-- Prove2me | Theorems.Thm_OAI_IndependentProducts_FiniteHead_stitched_path
-- name    : OAI.IndependentProducts.FiniteHead.stitched_path
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:37:25.295116+00:00
-- url     : https://prove2.me/theorems/76322cfe-0103-41f2-9c3b-463f92045033
-- title:
--   Path products of a stitched sample factor at the exit vertex
-- statement:
--   Let $\mathcal V$ be the tree of finite sequences of positive integers with root $\varnothing$, prefix order $\preceq$, parent map $u\mapsto u^-$ and nonroot vertices $\mathcal E=\mathcal V\setminus\{\varnothing\}$. For $v\in\mathcal V$ let $E(v)\subseteq\mathcal E$ be the set of its nonempty prefixes (the edges on the path from the root to $v$) and, for $\omega\in\mathbb R^{\mathcal E}$, let $\Pi_v(\omega)=\prod_{d\in E(v)}\omega(d)$ be the path product. Let $T$ be a finite head (a finite prefix-closed set of vertices containing $\varnothing$) with boundary $\partial T=\{e\in\mathcal E:e\notin T,\ e^-\in T\}$, let $\iota$ be a finite set, and let $i\mapsto e_i$ be an injective map $\iota\to\partial T$.
--
--   Given descendant samples $\sigma=(\sigma_i)_{i\in\iota}\in(\mathbb R^{\mathcal E})^\iota$, an exit sample $\xi\in\mathbb R^{\mathcal E}$ and an old sample $\omega\in\mathbb R^{\mathcal E}$, the stitched sample $S=S(\sigma,\xi,\omega)\in\mathbb R^{\mathcal E}$ is defined coordinatewise: for $d\in\mathcal E$,
--   $$
--   S(d)=\begin{cases}\xi(d)&\text{if }d=e_i,\\ \sigma_i(d)&\text{if }e_i\preceq d\text{ and }d\ne e_i,\\ \omega(d)&\text{if no }e_i\text{ is a prefix of }d,\end{cases}
--   $$
--   where in the first two cases $i$ is an index with $e_i\preceq d$ (it is unique, because distinct boundary vertices are incomparable and $i\mapsto e_i$ is injective).
--
--   **Theorem.** For every vertex $v$ and every $i\in\iota$ with $e_i\preceq v$,
--
--   $$
--   \Pi_v\big(S(\sigma,\xi,\omega)\big)=\Pi_{e_i^-}(\omega)\cdot\xi(e_i)\cdot\prod_{d\in E(v)\setminus E(e_i)}\sigma_i(d).
--   $$
--
--   So the path product of a vertex below the exit vertex $e_i$, evaluated on the stitched sample, factors into three independent pieces: the old head part up to the parent $e_i^-\in T$, the fresh multiplier on the exit vertex itself, and a residual product of the $i$-th descendant sample. This is what turns a tail polynomial, after resampling, into a first-exit sum with conditionally independent coefficients.
--
--   **Formalization Note** In Lean the input is the triple `z = ((σ, ξ), ω)` and the stitched sample is `T.stitched e z`, built from `sampleSelector` and `expandSamples`; the index $i$ in the definition is chosen with `Classical.choose`, and injectivity of `e` is an explicit hypothesis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/Resampling.lean#L105-L126

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
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling

open OAI OAI.IndependentProducts OAI.IndependentProducts.FiniteHead
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι
variable {ι : Type uι} [Fintype ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)

include he in
theorem OAI.IndependentProducts.FiniteHead.stitched_path (z : ((ι → Sample) × Sample) × Sample) (v : Vertex) (i : ι)
    (hi : (e i).val.val <+: v) :
    pathProduct v (T.stitched e z) = pathProduct (e i).val.val.dropLast z.2 * z.1.2 (e i).val *
      ∏ d ∈ pathEdges v \ pathEdges (e i).val.val, z.1.1 i d := by sorry

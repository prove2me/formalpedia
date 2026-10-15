-- Prove2me | Theorems.Thm_OAI_IndependentProducts_FiniteHead_integral_tailCoefficient
-- name    : OAI.IndependentProducts.FiniteHead.integral_tailCoefficient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:50:07.479416+00:00
-- url     : https://prove2.me/theorems/dc14ce0a-9c2b-4130-b30a-e025e70f3a01
-- title:
--   Tail coefficients average to their head-level part
-- statement:
--   Let $\mathcal V$ be the tree of finite sequences of positive integers with root $\varnothing$, prefix order $\preceq$, parent map $u\mapsto u^-$ and nonroot vertices $\mathcal E$. For $v\in\mathcal V$ let $E(v)=\{u\in\mathcal E:u\preceq v\}$ be its set of path edges and $\Pi_v(\omega)=\prod_{d\in E(v)}\omega(d)$ its path product on samples $\omega\in\mathbb R^{\mathcal E}$; for a vertex $v$ and an edge $f$ define the residual product $R_{v,f}(\omega)=\prod_{d\in E(v)\setminus E(f)}\omega(d)$. Let $T$ be a finite head (finite, prefix-closed, containing $\varnothing$) with boundary $\partial T=\{e\in\mathcal E:e\notin T,\ e^-\in T\}$.
--
--   Let $\iota,\kappa$ be finite sets and let $e:\iota\to\partial T$, $v:\kappa\to\mathcal V$, $j:\kappa\to\iota$ and $a:\kappa\to\mathbb R$ be arbitrary maps. The tail coefficient attached to an old sample $\omega$, an index $i\in\iota$ and a descendant sample $\sigma$ is
--   $$
--   B_i(\omega,\sigma)=\sum_{k\in\kappa:\ j(k)=i}a_k\,\Pi_{e_i^-}(\omega)\,R_{v_k,e_i}(\sigma).
--   $$
--
--   **Theorem.** Let $\mu$ be a probability measure on $\mathbb R$ with finite first moment and $\int w\,d\mu(w)=1$, and let $P_\mu=\mu^{\otimes\mathcal E}$. Then for every $\omega\in\mathbb R^{\mathcal E}$ and every $i\in\iota$,
--
--   $$
--   \int_{\mathbb R^{\mathcal E}}B_i(\omega,\sigma)\,dP_\mu(\sigma)=\sum_{k\in\kappa:\ j(k)=i}a_k\,\Pi_{e_i^-}(\omega).
--   $$
--
--   Residual products of mean-one multipliers have mean one, so averaging a tail coefficient over the descendant sample leaves only its head-level part. In the resampling argument this identifies the centering term of the first-exit sum with the path products of the head ancestors $e_i^-$ of the tail vertices.
--
--   **Formalization Note** The tail coefficient is `T.tailCoefficient e v j a ω i σ` and $R_{v,f}$ is `residualProduct v f`. The map $e$ need not be injective here. In Lean $E(v)$ is defined as the set of truncations of $v$ of lengths $1,\dots,|v|$, which is the same set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/TailCoefficients.lean#L136-L155

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
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients

open OAI OAI.IndependentProducts OAI.IndependentProducts.FiniteHead
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι uκ
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ] [DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)

theorem OAI.IndependentProducts.FiniteHead.integral_tailCoefficient {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (hm : ∫ w : ℝ, w ∂μ = 1)
    (old : Sample) (i : ι) :
    ∫ desc, T.tailCoefficient e v j a old i desc ∂productMeasure μ =
      ∑ k, if j k = i then a k * pathProduct (e i).val.val.dropLast old else 0 := by sorry

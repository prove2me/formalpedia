-- Prove2me | Theorems.Thm_OAI_IndependentProducts_representative_sum
-- name    : OAI.IndependentProducts.representative_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:48:08.50915+00:00
-- url     : https://prove2.me/theorems/192dc506-0833-46ef-b2aa-0f699f0af909
-- title:
--   Pointwise representatives of linear combinations in the $L^1$ product span
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$, let $P_\mu=\mu^{\otimes\mathcal E}$ be the product measure on the sample space $\mathbb R^{\mathcal E}$ indexed by the nonroot vertices $\mathcal E$ of the tree of finite sequences of positive integers, and let $X_\mu\subseteq L^1(P_\mu)$ be the closed real linear span of the path products. Let $\iota$ be a finite index set and, for each $i\in\iota$, let $x_i\in X_\mu$, let $f_i:\mathbb R^{\mathcal E}\to\mathbb R$ be a function with $x_i=f_i$ $P_\mu$-almost everywhere, and let $a_i\in\mathbb R$. Then
--
--   $$
--   \sum_{i\in\iota}a_i\,x_i\;=\;\sum_{i\in\iota}a_i\,f_i\qquad P_\mu\text{-almost everywhere}.
--   $$
--
--   That is, pointwise representatives of finitely many vectors of $X_\mu$ combine linearly into a representative of any linear combination of them. This bookkeeping lemma is used to compute norms and midpoint gains of explicit vectors, such as combinations of path products, through explicit functions on the sample space.
--
--   **Formalization Note** The left-hand side is the function underlying the $L^1$ class `(∑ i, a i • x i).val`. No moment assumption on $\mu$ is needed, and the $f_i$ are not assumed measurable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/TailCoefficients.lean#L20-L35

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

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι uκ
variable (μ : Measure ℝ) [hμprob : IsProbabilityMeasure μ]
  (h₂ : MemLp (fun w : ℝ => w) 2 μ)

omit hμprob in
theorem OAI.IndependentProducts.representative_sum [IsProbabilityMeasure μ] {ι : Type uι} [Fintype ι]
    (x : ι → productSpan μ)
    (f : ι → Sample → ℝ) (hf : ∀ i, (x i).val =ᵐ[productMeasure μ] f i) (a : ι → ℝ) :
    ((∑ i, a i • x i).val : Sample → ℝ) =ᵐ[productMeasure μ] fun ω => ∑ i, a i * f i ω := by sorry

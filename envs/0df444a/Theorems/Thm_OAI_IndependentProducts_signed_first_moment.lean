-- Prove2me | Theorems.Thm_OAI_IndependentProducts_signed_first_moment
-- name    : OAI.IndependentProducts.signed_first_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:23:13.433667+00:00
-- url     : https://prove2.me/theorems/46a5a1de-4291-4285-ab5d-3abff6f09736
-- title:
--   Signed first-moment bound for sums of random coefficients times mean-one multipliers
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb{R}$ with finite second moment $m_2(\mu)=\int_{\mathbb R}w^2\,d\mu(w)<\infty$ and mean $\int_{\mathbb R}w\,d\mu(w)=1$. Let $\iota$ be a finite index set and $(\Omega,\mathcal F)$ a measurable space; for each $i\in\iota$ let $\nu_i$ be a probability measure on $\Omega$ and $B_i:\Omega\to\mathbb R$ a measurable, $\nu_i$-integrable function. Sample $b=(b_i)_{i\in\iota}\in\Omega^\iota$ from the product measure $\nu=\bigotimes_{i\in\iota}\nu_i$ and, independently, $w=(w_i)_{i\in\iota}\in\mathbb R^\iota$ from $\mu^{\otimes\iota}$. Then
--
--   $$
--   \int_{\Omega^\iota\times\mathbb R^\iota}\Big|\sum_{i\in\iota}\Big(B_i(b_i)\,w_i-\int_\Omega B_i\,d\nu_i\Big)\Big|\,d(\nu\otimes\mu^{\otimes\iota})(b,w)\;\le\;2\sqrt{m_2(\mu)}\int_{\Omega^\iota}\Big(\sum_{i\in\iota}B_i(b_i)^2\Big)^{1/2}d\nu(b).
--   $$
--
--   The products $B_i(b_i)w_i$ are independent random variables and, because the multipliers have mean one, their means are $\int B_i\,d\nu_i$; so the left-hand side is the first absolute moment of a centered sum of independent terms. The inequality bounds it by the expected Euclidean length of the random coefficient vector $(B_i(b_i))_{i\in\iota}$, with a constant that depends on the multiplier law only through its second moment. It supplies the upper bound for first-exit sums in the $L^1$ span of products of independent mean-one multipliers along the paths of a tree, where $B_i$ is a coefficient produced by the coordinates below an exit vertex and $w_i$ is the fresh multiplier on that vertex.
--
--   **Formalization Note** The finite second moment is the hypothesis that the identity function lies in $L^2(\mu)$, and the Euclidean length $(\sum_i a_i^2)^{1/2}$ is the project's `euclidSize a`. The integral on the left is taken with respect to `(Measure.pi ν).prod (Measure.pi fun _ => μ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/CoefficientBounds.lean#L81-L133

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι
variable {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]

theorem OAI.IndependentProducts.signed_first_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun w : ℝ => w) 2 μ) (hmean : ∫ w : ℝ, w ∂μ = 1)
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (B : ι → Ω → ℝ) (hB : ∀ i, Integrable (B i) (ν i)) (hBm : ∀ i, Measurable (B i)) :
    (∫ z : (ι → Ω) × (ι → ℝ),
      |∑ i, (B i (z.1 i) * z.2 i - ∫ b, B i b ∂ν i)| ∂(Measure.pi ν).prod (Measure.pi (fun _ : ι => μ))) ≤
      2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ) *
        ∫ b : ι → Ω, euclidSize (fun i => B i (b i)) ∂Measure.pi ν := by sorry

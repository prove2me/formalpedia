-- Prove2me | Theorems.Thm_OAI_IndependentProducts_independent_centered_sum_abs_le
-- name    : OAI.IndependentProducts.independent_centered_sum_abs_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:22:31.753312+00:00
-- url     : https://prove2.me/theorems/a4c207f9-1422-453f-8098-de7a3fdc01ce
-- title:
--   The first absolute moment of a centered sum of independent variables is at most twice the expected Euclidean norm
-- statement:
--   Let $\iota$ be a finite index set and, for each $i\in\iota$, let $\nu_i$ be a probability measure on $\mathbb{R}$ with finite first moment; write $m_i=\int z\,d\nu_i(z)$ for its mean. Let $\nu=\bigotimes_{i\in\iota}\nu_i$ be the product measure on $\mathbb{R}^\iota$, i.e. the law of a vector $X=(X_i)_{i\in\iota}$ with independent coordinates $X_i\sim\nu_i$, and let $\|x\|_2=\bigl(\sum_{i\in\iota}x_i^2\bigr)^{1/2}$ be the Euclidean norm on $\mathbb{R}^\iota$. Then
--
--   $$\int_{\mathbb{R}^\iota}\Bigl|\sum_{i\in\iota}\bigl(x_i-m_i\bigr)\Bigr|\,d\nu(x)\ \le\ 2\int_{\mathbb{R}^\iota}\|x\|_2\,d\nu(x),$$
--
--   that is, $\mathbb{E}\bigl|\sum_i(X_i-m_i)\bigr|\le2\,\mathbb{E}\|X\|_2$.
--
--   This symmetrization inequality controls the $L^1$ size of a sum of independent, not necessarily identically distributed, centered real variables by the expected Euclidean norm of the uncentered vector, assuming only first moments. It is the probabilistic input for first-moment bounds on centered sums of the form $\sum_i\bigl(B_iW_i-\mathbb{E}[B_iW_i]\bigr)$ that arise from first-exit decompositions of linear combinations of path products.
--
--   **Formalization Note** The Euclidean norm is `euclidSize x` and the product measure is `Measure.pi ν`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/RandomSigns.lean#L219-L250

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
variable {ι : Type uι} [Fintype ι]

theorem OAI.IndependentProducts.independent_centered_sum_abs_le (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (fun x : ℝ => x) (ν i)) :
    (∫ x : ι → ℝ, |∑ i, (x i - ∫ z : ℝ, z ∂ν i)| ∂Measure.pi ν) ≤
      2 * ∫ x : ι → ℝ, euclidSize x ∂Measure.pi ν := by sorry

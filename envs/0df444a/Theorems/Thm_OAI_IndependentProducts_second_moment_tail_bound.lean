-- Prove2me | Theorems.Thm_OAI_IndependentProducts_second_moment_tail_bound
-- name    : OAI.IndependentProducts.second_moment_tail_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:10:41.791221+00:00
-- url     : https://prove2.me/theorems/5fce6001-4e87-441c-8efa-afe35c4c2557
-- title:
--   A Paley-Zygmund type lower bound for the probability of exceeding a level
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space and let $V:\Omega\to\mathbb{R}$ be a measurable function with $V(\omega)\ge0$ for every $\omega\in\Omega$ and $\mathbb{E}[V^2]<\infty$. Let $a,b\in\mathbb{R}$ satisfy $0\le a<b\le\mathbb{E}[V]$. Then
--
--   $$(b-a)^2\ \le\ \mathbb{E}\bigl[V^2\bigr]\cdot\mu\bigl\{\omega\in\Omega:\ V(\omega)\ge a\bigr\}.$$
--
--   When $\mathbb{E}[V]>0$, the choice $a=\mathbb{E}[V]/2$, $b=\mathbb{E}[V]$ gives the Paley-Zygmund inequality $\mu\{V\ge\mathbb{E}[V]/2\}\ge(\mathbb{E}[V])^2/(4\,\mathbb{E}[V^2])$. Such second-moment lower bounds show that nonnegative variables with controlled second moments exceed a fixed fraction of their mean with probability bounded away from zero.
--
--   **Formalization Note** Nonnegativity is assumed pointwise rather than almost surely, $V$ is assumed measurable, square integrability is `MemLp V 2 μ`, and the probability is the real-valued measure `μ.real`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean#L124-L159

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

theorem OAI.IndependentProducts.second_moment_tail_bound (V : Ω → ℝ) (hV : MemLp V 2 μ)
    (hVmeas : Measurable V) (hpos : ∀ ω, 0 ≤ V ω)
    (a b : ℝ) (ha : 0 ≤ a) (hb : a < b) (hmean : b ≤ ∫ ω, V ω ∂μ) :
    (b - a) ^ 2 ≤ (∫ ω, V ω ^ 2 ∂μ) * μ.real {ω | a ≤ V ω} := by sorry

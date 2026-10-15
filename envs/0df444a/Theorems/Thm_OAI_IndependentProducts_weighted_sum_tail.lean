-- Prove2me | Theorems.Thm_OAI_IndependentProducts_weighted_sum_tail
-- name    : OAI.IndependentProducts.weighted_sum_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:15:01.189267+00:00
-- url     : https://prove2.me/theorems/212a7251-a290-4491-b0cd-3eccedaf1011
-- title:
--   A weighted sum of nonnegative unit-mean variables exceeds half its mean with probability at least $1/(4M)$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $\iota$ a finite index set, and $a\in\mathbb{R}^\iota$ with $S=\sum_{i\in\iota}a_i^2>0$. Let $M>0$, and let $U_i:\Omega\to\mathbb{R}$ $(i\in\iota)$ be measurable, square integrable functions such that for every $i\in\iota$:
--
--   1. $U_i(\omega)\ge0$ for all $\omega\in\Omega$;
--   2. $\mathbb{E}[U_i]=1$;
--   3. $\mathbb{E}[U_i^2]\le M$.
--
--   Then
--
--   $$P\Bigl\{\omega\in\Omega:\ \sum_{i\in\iota}a_i^2\,U_i(\omega)\ \ge\ \frac{S}{2}\Bigr\}\ \ge\ \frac{1}{4M}.$$
--
--   No independence between the $U_i$ is assumed. The typical application is $U_i=Z_i^2$ for standard Gaussians $Z_i$, where $M=3$ and the bound $1/12$ says that the random quadratic form $\sum_ia_i^2Z_i^2$ is at least half its mean with probability bounded away from zero, uniformly in the weights and in the number of terms.
--
--   **Formalization Note** The probability is the real-valued measure `P.real`; square integrability is `MemLp (U i) 2 P`, and nonnegativity is assumed pointwise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/GaussianMoments.lean#L54-L74

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
variable {P : Measure Ω}
variable [IsProbabilityMeasure P]

theorem OAI.IndependentProducts.weighted_sum_tail (a : ι → ℝ) (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 P) (hmeas : ∀ i, Measurable (U i))
    (hpos : ∀ i ω, 0 ≤ U i ω) (hm : ∀ i, ∫ ω, U i ω ∂P = 1)
    (M : ℝ) (hM : 0 < M) (hm2 : ∀ i, (∫ ω, U i ω ^ 2 ∂P) ≤ M)
    (ha : 0 < ∑ i, a i ^ 2) :
    1 / (4 * M) ≤ P.real {ω | (∑ i, a i ^ 2) / 2 ≤ ∑ i, a i ^ 2 * U i ω} := by sorry

-- Prove2me | Theorems.Thm_OAI_IndependentProducts_map_gaussian_weighted_sum
-- name    : OAI.IndependentProducts.map_gaussian_weighted_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:13:00.267356+00:00
-- url     : https://prove2.me/theorems/049c9dea-dcca-4111-b2f7-049f20573d07
-- title:
--   A weighted sum of independent standard Gaussians is centered Gaussian with variance $\sum_i a_i^2$
-- statement:
--   Let $\iota$ be a finite index set, let $\gamma^{\otimes\iota}$ be the standard Gaussian measure on $\mathbb{R}^\iota$ (the product of copies of $N(0,1)$), and let $a=(a_i)_{i\in\iota}\in\mathbb{R}^\iota$. Then the image of $\gamma^{\otimes\iota}$ under the linear functional $x\mapsto\sum_{i\in\iota}a_ix_i$ is the centered Gaussian law with variance $\sum_ia_i^2$:
--
--   $$\gamma^{\otimes\iota}\circ\Bigl(x\mapsto\sum_{i\in\iota}a_ix_i\Bigr)^{-1}=N\Bigl(0,\ \sum_{i\in\iota}a_i^2\Bigr).$$
--
--   Equivalently, if $(Z_i)_{i\in\iota}$ are independent standard Gaussians, then $\sum_ia_iZ_i\sim N\bigl(0,\sum_ia_i^2\bigr)$.
--
--   This stability property of Gaussian laws is used to identify the law of a linear form in a Gaussian vector, for instance the conditional law of a Gaussian bilinear form $\sum_ia_ix_iH_i$ when one of the two Gaussian vectors is fixed.
--
--   **Formalization Note** The variance is written as a sum of nonnegative reals `NNReal.mk (a i ^ 2) _`, as required by Mathlib's `gaussianReal`. When the variance is $0$ (all $a_i=0$, or $\iota$ empty), $N(0,0)$ is the Dirac mass at $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean#L263-L279

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
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]
variable [Fintype ι]

theorem OAI.IndependentProducts.map_gaussian_weighted_sum (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x => ∑ i, a i * x i) =
      gaussianReal 0 (∑ i, NNReal.mk (a i ^ 2) (sq_nonneg _)) := by sorry

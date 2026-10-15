-- Prove2me | Theorems.Thm_OAI_IndependentProducts_exponential_scalar_excess
-- name    : OAI.IndependentProducts.exponential_scalar_excess
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:54:12.049528+00:00
-- url     : https://prove2.me/theorems/37aaf73f-329f-44cc-ad83-e75d9e4e3f39
-- title:
--   Excess lower bound for affine forms in independent exponential variables
-- statement:
--   Let $\iota$ be a finite index set and let $U=(U_i)_{i\in\iota}$ be a random vector with independent coordinates, each having the standard exponential law $\mathrm{Exp}(1)$ (density $e^{-u}$ on $(0,\infty)$); write $\mathbb E$ for expectation with respect to this product law. For real $t,r,z$ put $\operatorname{exc}_{t,r}(z)=\max(t|z|-r,\,0)$, and for $K\in\mathbb R$ let
--
--   $$
--   c(K)=\frac1{16}\,\mathbb E\big[\max(|G|-2K,\,0)\big],\qquad G\sim N(0,1),
--   $$
--
--   be the Gaussian excess constant.
--
--   **Theorem.** For every $a\in\mathbb R^\iota$ and all real numbers $b,K,t,r$ with $K>0$, $t\ge 0$ and $r\ge 0$,
--
--   $$
--   t\,c(K)\,\sqrt{\sum_{i\in\iota}a_i^2}\;-\;\frac{c(K)}{K}\,r\;\le\;\mathbb E\Big[\operatorname{exc}_{t,r}\Big(b+\sum_{i\in\iota}a_iU_i\Big)\Big].
--   $$
--
--   The bound is uniform in the shift $b$ and in the number of variables: the expected excess of an affine form in independent exponentials over a threshold proportional to the Euclidean norm of its coefficients is bounded below in terms of the Gaussian constant $c(K)$ alone. With $A=t\,c(K)$ and $D=c(K)/K$ this is exactly the scalar hypothesis needed to bound the averaged midpoint modulus of the $L^1$ product span with exponential multipliers.
--
--   **Formalization Note** The product law is `exponentialVector`, i.e. `Measure.pi` of copies of `exponentialLaw` (Mathlib's `expMeasure 1`); $c(K)$ is `excessConstant K` and $\operatorname{exc}_{t,r}$ is `excess t r`. The index type $\iota$ may live in any universe.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ExponentialExcess.lean#L176-L203

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
import Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialLaw
import Definitions.Def_OAI_Analysis_ProductSpaces_ExponentialMixture

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι

theorem OAI.IndependentProducts.exponential_scalar_excess {ι : Type uι} [Fintype ι] (a : ι → ℝ) (b K t r : ℝ)
    (hK : 0 < K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (t * excessConstant K) * Real.sqrt (∑ i, a i ^ 2) - (excessConstant K / K) * r ≤
      ∫ u : ι → ℝ, excess t r (b + ∑ i, a i * u i) ∂exponentialVector := by sorry

-- Prove2me | Theorems.Thm_OAI_IndependentProducts_gaussian_bilinear_excess
-- name    : OAI.IndependentProducts.gaussian_bilinear_excess
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:21:41.919823+00:00
-- url     : https://prove2.me/theorems/8b3c1f45-9b55-4dae-be18-399d14abfd72
-- title:
--   Lower bound for the expected excess of a Gaussian bilinear form
-- statement:
--   Let $\iota$ be a finite index set and let $G=(G_i)_{i\in\iota}$ and $H=(H_i)_{i\in\iota}$ be independent standard Gaussian vectors in $\mathbb{R}^\iota$, so that all $2|\iota|$ coordinates are independent $N(0,1)$ variables; formally, expectations are taken with respect to $\gamma^{\otimes\iota}\otimes\gamma^{\otimes\iota}$ on $\mathbb{R}^\iota\times\mathbb{R}^\iota$, where $\gamma=N(0,1)$. For $t,r,z\in\mathbb{R}$ let $\operatorname{exc}_{t,r}(z)=\max(t|z|-r,0)$, and for $s\in\mathbb{R}$ let
--
--   $$g(s)=\mathbb{P}\bigl(|Z|\ge s\bigr),\qquad Z\sim N(0,1),$$
--
--   be the two-sided Gaussian tail. Let $a\in\mathbb{R}^\iota$ and $K,t,r\ge0$, and write $\|a\|_2=\bigl(\sum_ia_i^2\bigr)^{1/2}$. Then
--
--   $$\frac{g(\sqrt2\,K)}{12}\;\operatorname{exc}_{t,r}\bigl(K\,\|a\|_2\bigr)\ \le\ \mathbb{E}\Bigl[\operatorname{exc}_{t,r}\Bigl(\sum_{i\in\iota}a_i\,G_i\,H_i\Bigr)\Bigr].$$
--
--   The bilinear Gaussian chaos $\sum_ia_iG_iH_i$ is what a symmetrized weighted sum of squared Gaussians becomes after polarization. The estimate says that its expected excess over any level $r\ge0$ is at least a fixed proportion of the excess at the deterministic scale $K\|a\|_2$, uniformly in the dimension and the weights; it is the key scalar input for the explicit lower bounds on the averaged asymptotic midpoint modulus when the multipliers are squared Gaussians.
--
--   **Formalization Note** The tail is `gaussianTail s`, the real number $\gamma\{x: s\le|x|\}$, and $\gamma^{\otimes\iota}$ is `gaussianVector`, the product of copies of `gaussianReal 0 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/GaussianMoments.lean#L265-L304

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
variable {ι : Type uι} [Fintype ι]

theorem OAI.IndependentProducts.gaussian_bilinear_excess (a : ι → ℝ) (K t r : ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (gaussianTail (Real.sqrt 2 * K) / 12) *
      excess t r (K * Real.sqrt (∑ i, a i ^ 2)) ≤
      ∫ z : (ι → ℝ) × (ι → ℝ), excess t r (∑ i, a i * z.1 i * z.2 i)
        ∂gaussianVector.prod gaussianVector := by sorry

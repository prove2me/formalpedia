-- Prove2me | Theorems.Thm_OAI_IndependentProducts_gaussian_integral_fourth
-- name    : OAI.IndependentProducts.gaussian_integral_fourth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:09:36.227907+00:00
-- url     : https://prove2.me/theorems/4ee92b23-2cf7-4d7c-8744-bdd02edb73f3
-- title:
--   The fourth moment of a standard Gaussian equals 3
-- statement:
--   Let $N(0,1)$ denote the standard Gaussian distribution on $\mathbb{R}$. Then
--
--   $$\int_{\mathbb{R}}x^4\,dN(0,1)(x)=\int_{\mathbb{R}}x^4\,\frac{e^{-x^2/2}}{\sqrt{2\pi}}\,dx=3,$$
--
--   that is, $\mathbb{E}[Z^4]=3$ for $Z\sim N(0,1)$.
--
--   This classical moment identity feeds second-moment arguments for Gaussian quadratic forms: for independent standard Gaussians $Z_i$ the squares $Z_i^2$ have mean $1$ and second moment $3$, which via a Paley-Zygmund type bound shows that a weighted sum $\sum_ia_i^2Z_i^2$ is at least half its mean with probability at least $1/12$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean#L59-L96

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

theorem OAI.IndependentProducts.gaussian_integral_fourth : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by sorry

-- Prove2me | Theorems.Thm_OAI_IndependentProducts_measurePreserving_gaussianRotate
-- name    : OAI.IndependentProducts.measurePreserving_gaussianRotate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:12:20.499337+00:00
-- url     : https://prove2.me/theorems/6312ba41-74b8-49a7-9084-5e8912270dc4
-- title:
--   The map $(z_1,z_2)\mapsto\bigl((z_1+z_2)/\sqrt2,\,(z_1-z_2)/\sqrt2\bigr)$ preserves the standard Gaussian measure on the plane
-- statement:
--   Let $\gamma=N(0,1)$ be the standard Gaussian law on $\mathbb{R}$ and $\gamma\otimes\gamma$ the standard Gaussian measure on $\mathbb{R}^2=\mathbb{R}\times\mathbb{R}$. Define $R:\mathbb{R}^2\to\mathbb{R}^2$ by
--
--   $$R(z_1,z_2)=\Bigl(\frac{z_1+z_2}{\sqrt2},\ \frac{z_1-z_2}{\sqrt2}\Bigr).$$
--
--   Then $R$ is measurable and preserves $\gamma\otimes\gamma$, i.e. the image measure of $\gamma\otimes\gamma$ under $R$ is $\gamma\otimes\gamma$ again. Equivalently, if $Z_1,Z_2$ are independent standard Gaussians, then $(Z_1+Z_2)/\sqrt2$ and $(Z_1-Z_2)/\sqrt2$ are again independent standard Gaussians.
--
--   The map $R$ is an orthogonal linear map of the plane (a reflection), and the statement is the polarization step for products of independent Gaussians: it rewrites a difference of squares $\tfrac12(Z_1^2-Z_2^2)$ as the product $\frac{Z_1+Z_2}{\sqrt2}\cdot\frac{Z_1-Z_2}{\sqrt2}$ of two new independent standard Gaussians. This is how symmetrized sums of squared Gaussians are turned into Gaussian bilinear forms.
--
--   **Formalization Note** The map is `gaussianRotate`, and Lean's `MeasurePreserving` includes measurability of the map together with the equality of image measures.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean#L172-L235

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

theorem OAI.IndependentProducts.measurePreserving_gaussianRotate : MeasurePreserving gaussianRotate
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by sorry

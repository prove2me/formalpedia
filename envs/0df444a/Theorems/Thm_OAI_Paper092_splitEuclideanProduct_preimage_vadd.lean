-- Prove2me | Theorems.Thm_OAI_Paper092_splitEuclideanProduct_preimage_vadd
-- name    : OAI.Paper092.splitEuclideanProduct_preimage_vadd
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:21:09.943026+00:00
-- url     : https://prove2.me/theorems/e7ca3feb-216a-479e-bd11-9dc8ef275275
-- title:
--   Splitting $\mathbb{R}^{r+s}$ as $\mathbb{R}^r\times\mathbb{R}^s$ commutes with translating both factors
-- statement:
--   For $r,s\in\mathbb{N}$ let $\Phi_{r,s}:\mathbb{R}^{r+s}\to\mathbb{R}^r\times\mathbb{R}^s$ be the linear isomorphism that splits a vector into its first $r$ and its last $s$ coordinates,
--   $\Phi_{r,s}(x)=\big((x_0,\dots,x_{r-1}),\,(x_r,\dots,x_{r+s-1})\big)$.
--   For a vector $a$ and a set $A$ write $a+A=\{a+x: x\in A\}$.
--
--   **Theorem.** For all $a\in\mathbb{R}^r$, $b\in\mathbb{R}^s$ and all subsets $A\subseteq\mathbb{R}^r$, $B\subseteq\mathbb{R}^s$,
--   $$
--   \Phi_{r,s}^{-1}\big((a+A)\times(b+B)\big)=\Phi_{r,s}^{-1}(a,b)+\Phi_{r,s}^{-1}(A\times B).
--   $$
--
--   No assumptions on $A$ and $B$ are needed. The identity pulls a translation out of a product set in $\mathbb{R}^{r+s}$; combined with translation invariance of Lebesgue and Hausdorff measures, it reduces the area of a product of a translated facet with a simplex to the area of an untranslated linear image.
--
--   **Formalization Note** $\Phi_{r,s}$ is `splitEuclideanProduct r s`, a continuous linear equivalence from `Euclidean (r + s)` to `Euclidean r × Euclidean s`; $a+A$ is the pointwise translation `a +ᵥ A`, and $\Phi_{r,s}^{-1}(a,b)$ is `(splitEuclideanProduct r s).symm (a, b)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProductFacetAreas.lean#L122-L141

import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductVolumeGeneral
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductFacetAreas

open OAI OAI.Paper092
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal Pointwise

theorem OAI.Paper092.splitEuclideanProduct_preimage_vadd {r s : ℕ}
    (a : Euclidean r) (b : Euclidean s) (A : Set (Euclidean r)) (B : Set (Euclidean s)) :
    splitEuclideanProduct r s ⁻¹' ((a +ᵥ A) ×ˢ (b +ᵥ B)) =
      (splitEuclideanProduct r s).symm (a, b) +ᵥ
        (splitEuclideanProduct r s ⁻¹' (A ×ˢ B)) := by sorry

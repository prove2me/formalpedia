-- Prove2me | Theorems.Thm_OAI_Paper092_simplexProduct_diagonal_facet_area_right
-- name    : OAI.Paper092.simplexProduct_diagonal_facet_area_right
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:22:42.603506+00:00
-- url     : https://prove2.me/theorems/4ac9347a-1a23-44cf-a260-434602d57617
-- title:
--   Area of the facet of $\Delta_r\times\Delta_{s+1}$ over the slanted facet of the second factor is $\sqrt{s+1}/(r!\,s!)$
-- statement:
--   Let $\Delta_m=\{x\in\mathbb{R}^m: x_j\ge0,\ \sum_j x_j\le1\}$ be the standard simplex (the convex hull of $0$ and the unit vectors) and let $F_\ast^{(m)}=\{y\in\Delta_m: \sum_k y_k=1\}$ be its slanted facet. Let $\Phi_{p,q}:\mathbb{R}^{p+q}\to\mathbb{R}^p\times\mathbb{R}^q$ split a vector into its first $p$ and its last $q$ coordinates. For $d\in\mathbb{N}$ let $\mathcal H^d$ denote the $d$-dimensional Hausdorff measure on Euclidean space, normalized so that it agrees with $d$-dimensional Lebesgue measure on $d$-dimensional affine subspaces.
--
--   **Theorem.** For all $r,s\in\mathbb{N}$ (zero allowed), the set $\Phi_{r,s+1}^{-1}\big(\Delta_r\times F_\ast^{(s+1)}\big)\subset\mathbb{R}^{r+(s+1)}$ satisfies
--   $$
--   \mathcal H^{r+s}\Big(\Phi_{r,s+1}^{-1}\big(\Delta_r\times F_\ast^{(s+1)}\big)\Big)=\sqrt{s+1}\cdot\frac{1}{r!}\cdot\frac{1}{s!}.
--   $$
--
--   The set is the facet of the product polytope $\Delta_r\times\Delta_{s+1}$ on which the coordinates of the second factor sum to $1$. Its area is the volume $1/r!$ of $\Delta_r$ times the $s$-dimensional area $\sqrt{s+1}/s!$ of the slanted facet of $\Delta_{s+1}$. With $r=10$ and $s=9$ it gives the area $\sqrt{10}/(10!\,9!)$ of the slanted second-block facet of $\Delta_{10}\times\Delta_{10}\subset\mathbb{R}^{20}$.
--
--   **Formalization Note** $\mathcal H^d$ is Mathlib's `MeasureTheory.Measure.euclideanHausdorffMeasure d` (notation `μHE[d]`), with values in $[0,\infty]$; the right-hand side is the corresponding real number, embedded by `ENNReal.ofReal`. $\Phi_{p,q}$ is `splitEuclideanProduct p q`, $\Delta_m$ is `standardSimplex m` and $F_\ast^{(m)}$ is `simplexFacet m none`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProductFacetAreas.lean#L199-L215

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

theorem OAI.Paper092.simplexProduct_diagonal_facet_area_right (r s : ℕ) :
    μHE[r + s] (splitEuclideanProduct r (s + 1) ⁻¹'
      (standardSimplex r ×ˢ simplexFacet (s + 1) none)) =
      ENNReal.ofReal (Real.sqrt (s + 1) *
        ((1 / (Nat.factorial r : ℝ)) * (1 / (Nat.factorial s : ℝ)))) := by sorry

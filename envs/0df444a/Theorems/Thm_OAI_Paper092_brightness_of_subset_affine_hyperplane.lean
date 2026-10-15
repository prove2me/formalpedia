-- Prove2me | Theorems.Thm_OAI_Paper092_brightness_of_subset_affine_hyperplane
-- name    : OAI.Paper092.brightness_of_subset_affine_hyperplane
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:23:46.391961+00:00
-- url     : https://prove2.me/theorems/e6d7f764-ae6f-4d64-8943-9499813ac6f9
-- title:
--   Brightness of a set lying in a hyperplane: $|\langle u,v\rangle|$ times its $(n-1)$-dimensional area
-- statement:
--   Work in $\mathbb{R}^n$ with the standard inner product. For $u\in\mathbb{R}^n$ let $u^\perp=\{y:\langle u,y\rangle=0\}$ (the orthogonal complement of the span of $u$; all of $\mathbb{R}^n$ when $u=0$), let $\pi_u:\mathbb{R}^n\to u^\perp$ be the orthogonal projection, and let $\mathrm{vol}_{u^\perp}$ be the Lebesgue measure of the inner product space $u^\perp$. The brightness of a set $K\subseteq\mathbb{R}^n$ in direction $u$ is
--   $$
--   b_K(u)=\|u\|\cdot\mathrm{vol}_{u^\perp}\big(\pi_u(K)\big);
--   $$
--   for a unit vector $u$ this is the volume of the shadow of $K$ on the hyperplane $u^\perp$. Let $\mathcal H^{n-1}$ be the $(n-1)$-dimensional Hausdorff measure on $\mathbb{R}^n$, normalized to agree with Lebesgue measure on hyperplanes.
--
--   **Theorem.** Let $v\in\mathbb{R}^n$ with $\|v\|=1$, let $c\in\mathbb{R}$, and let $S\subseteq\mathbb{R}^n$ be any set such that $\langle v,x\rangle=c$ for all $x\in S$. Then for every $u\in\mathbb{R}^n$
--   $$
--   b_S(u)=|\langle u,v\rangle|\cdot\mathcal H^{n-1}(S).
--   $$
--
--   Thus the shadow of a flat piece $S$ of the hyperplane $\{x:\langle v,x\rangle=c\}$ has the area of $S$ multiplied by $|\cos\angle(u,v)|$, scaled by $\|u\|$. Applied to the facets of a polytope, which lie in hyperplanes, it computes the brightness of each facet from its area and its unit normal.
--
--   **Formalization Note** Both measures take values in $[0,\infty]$ and enter the statement through `ENNReal.toReal`, so an infinite value is read as $0$; the identity holds with this convention, and no measurability of $S$ is assumed. Here $b_K(u)$ is `brightness K u`, defined as the norm of $u$ times `(projectionVolume K u).toReal`; $u^\perp$ is `normalHyperplane u`, and $\mathcal H^{n-1}$ is `μHE[n - 1]`. The natural-number subtraction $n-1$ is harmless because $\|v\|=1$ forces $n\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProjectionJacobian.lean#L143-L157

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
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProjectionJacobian

open OAI OAI.Paper092
universe uι
open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

theorem OAI.Paper092.brightness_of_subset_affine_hyperplane {n : ℕ} (u v : Euclidean n)
    (hv : ‖v‖ = 1) (c : ℝ) (S : Set (Euclidean n))
    (hS : ∀ x ∈ S, ⟪v, x⟫ = c) :
    brightness S u = |⟪u, v⟫| * (μHE[n - 1] S).toReal := by sorry

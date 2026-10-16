-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_euclidean_affine_geodesic
-- name    : OAI.ThreeManifold.RiemannianCoordinates.euclidean_affine_geodesic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:56:14.986223+00:00
-- url     : https://prove2.me/theorems/858d573e-bfad-412a-ae8d-d44a4bd64a0d
-- title:
--   Affine reparametrizations of geodesics in $\mathbb{R}^3$ are geodesics
-- statement:
--   Let $g$ be any smooth Riemannian metric on $\mathbb R^3$, regarded as a smooth manifold with its single identity chart, so that tangent vectors are elements of $\mathbb R^3$. For an open set $U\subseteq\mathbb R$, a curve $\gamma:\mathbb R\to\mathbb R^3$ is a geodesic of $g$ on $U$ if it is $C^\infty$ on $U$ and
--   $$\ddot\gamma(s)+\Gamma_{\gamma(s)}\big(\dot\gamma(s),\dot\gamma(s)\big)=0\qquad(s\in U),$$
--   where $\Gamma_x(u,w)^i=\sum_{j,k}\Gamma^i_{jk}(x)\,u^jw^k$ is formed with the Christoffel symbols of $g$.
--
--   **Statement.** If $U\subseteq\mathbb R$ is open and $\gamma$ is a geodesic of $g$ on $U$, then for all $a,k\in\mathbb R$ the reparametrized curve $s\mapsto\gamma(a+ks)$ is a geodesic of $g$ on the preimage
--   $$U_{a,k}=\{s\in\mathbb R:\ a+ks\in U\}.$$
--
--   No restriction is placed on $k$: for $k=0$ the curve is constant. The result is used to normalize geodesics to unit speed ($k>0$) and to reverse their orientation ($k=-1$) without leaving the class of geodesics.
--
--   **Formalization Note** `IsGeodesicOn g γ U` demands smoothness on $U$ and the geodesic equation in every chart of the atlas; for the model space `E3` the atlas consists of the identity chart only, which reduces the condition to the equation displayed above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean#L644-L668

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages
import Definitions.Def_OAI_Geometry_ConjugatePoints_NoConjugatePoints

open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
open CompactMetric

theorem OAI.ThreeManifold.RiemannianCoordinates.euclidean_affine_geodesic (g : SmoothMetric E3) {γ : ℝ → E3} {U : Set ℝ}
    (hU : IsOpen U) (hγ : IsGeodesicOn g γ U) (a k : ℝ) :
    IsGeodesicOn g (fun s => γ (a+k*s)) ((fun s : ℝ => a+k*s) ⁻¹' U) := by sorry

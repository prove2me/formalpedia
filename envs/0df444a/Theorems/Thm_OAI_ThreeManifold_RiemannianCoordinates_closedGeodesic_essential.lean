-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_closedGeodesic_essential
-- name    : OAI.ThreeManifold.RiemannianCoordinates.closedGeodesic_essential
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:58:57.030099+00:00
-- url     : https://prove2.me/theorems/b80f5355-5ffb-41ae-945b-374d5c6a230a
-- title:
--   Without conjugate points, a nonconstant geodesic loop is never null-homotopic
-- statement:
--   Let $M$ be a compact Hausdorff smooth 3-manifold (modelled on $\mathbb{R}^3$) with a smooth Riemannian metric $g$ that has *no conjugate points*. This means: for every open set $U\subseteq\mathbb{R}$ that is an interval, every smooth geodesic $\sigma$ on $U$ and every Jacobi field $J$ along $\sigma$ on $U$, if $J$ vanishes at two distinct points of $U$, then $J$ vanishes on all of $U$. Here geodesics and Jacobi fields are defined through the geodesic and Jacobi equations in every atlas chart.
--
--   Let $\gamma:\mathbb{R}\to M$ be a geodesic defined on all of $\mathbb{R}$, that is, $\gamma$ is $C^\infty$ and satisfies the geodesic equation in every chart. Assume $\gamma(1)=\gamma(0)$ and $\gamma'(0)\neq 0$. Then the loop $\gamma|_{[0,1]}$, based at $\gamma(0)$, represents a nontrivial element of the fundamental group:
--   $$
--   \big[\gamma|_{[0,1]}\big]\neq 1\quad\text{in } \pi_1\big(M,\gamma(0)\big).
--   $$
--
--   Only $\gamma(1)=\gamma(0)$ is required, not $\gamma'(1)=\gamma'(0)$, so the statement covers every nonconstant geodesic loop and in particular every closed geodesic. It is the no-conjugate-points analogue of the classical fact that on a manifold of nonpositive curvature no nonconstant geodesic loop is contractible, and it lets geodesic loops detect nontrivial elements of $\pi_1(M)$.
--
--   **Formalization Note** The loop is `closedCurvePath`, the restriction of $\gamma$ to the unit interval regarded as a `Path (γ 0) (γ 0)`, and the conclusion compares its class with `1` in `FundamentalGroup M (γ 0)`. The velocity $\gamma'(0)$ is the manifold derivative, an element of the model space $\mathbb{R}^3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Continuation.lean#L867-L894

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

open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

theorem OAI.ThreeManifold.RiemannianCoordinates.closedGeodesic_essential (g : SmoothMetric M) (hn : NoConjugatePoints g)
    {γ : ℝ → M} (hγ : IsGeodesicOn g γ univ) (he : γ 1 = γ 0)
    (hv : (velocity γ 0 : E3) ≠ 0) :
    (Path.Homotopic.Quotient.mk (closedCurvePath (contMDiffOn_univ.mp hγ.1).continuous he) :
      FundamentalGroup M (γ 0)) ≠ (1 : FundamentalGroup M (γ 0)) := by sorry

-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_geodesic_of_acceleration_zero
-- name    : OAI.ThreeManifold.RiemannianCoordinates.geodesic_of_acceleration_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:53:08.138797+00:00
-- url     : https://prove2.me/theorems/45f6dbb8-bc6c-4827-8239-4be99d3eb655
-- title:
--   A smooth curve with vanishing covariant acceleration is a geodesic in every chart
-- statement:
--   Let $M$ be a smooth ($C^\infty$) manifold modelled on $\mathbb{R}^3$ with a smooth Riemannian metric $g$. For an atlas chart $c$ and $y$ in its target let $\Gamma^i_{jk}(y)$ be the Christoffel symbols of the coordinate metric matrix $g_{ij}(y) = g(\partial_i, \partial_j)$ of $c$, and $\Gamma_c(y)(u, w)^i = \sum_{j,k}\Gamma^i_{jk}(y)\,u^j w^k$. For a curve $\gamma : \mathbb{R} \to M$ the velocity field is $\dot\gamma(s) = d\gamma_s(1) \in T_{\gamma(s)}M$. For a vector field $J$ along $\gamma$ with chart coordinates $\hat J_c(s) = dc_{\gamma(s)} J(s)$, the covariant derivative is computed in the preferred chart $c$ at $\gamma(s)$: with $x = c\circ\gamma$,
--   $$
--   \frac{DJ}{ds}(s) = d(c^{-1})_{x(s)}\Big(\hat J_c'(s) + \Gamma_c(x(s))\big(x'(s), \hat J_c(s)\big)\Big).
--   $$
--   A curve is a geodesic on $U \subseteq \mathbb{R}$ if it is $C^\infty$ on $U$ and, for every atlas chart $c$ and every $s \in U$ with $\gamma(s)$ in the source of $c$, the coordinate curve $x = c\circ\gamma$ satisfies $x''(s) + \Gamma_c(x(s))\big(x'(s), x'(s)\big) = 0$.
--
--   **Theorem.** Let $U \subseteq \mathbb{R}$ be open and $\gamma : \mathbb{R} \to M$ be $C^\infty$ on $U$. If
--   $$
--   \frac{D\dot\gamma}{ds}(s) = 0 \qquad \text{for all } s \in U,
--   $$
--   then $\gamma$ is a geodesic on $U$.
--
--   The covariant derivative is defined through one preferred chart at each point, whereas the geodesic condition is required in every chart of the atlas. The theorem bridges the two, so geodesics can be recognised intrinsically, for example as images of geodesics under local isometries.
--
--   **Formalization Note** The geodesic predicate is `IsGeodesicOn`, in which $x''$ is written as `deriv (deriv (c ∘ γ))` through `alongDerivative`; the velocity is `velocity γ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Curvature.lean#L327-L341

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

open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

theorem OAI.ThreeManifold.RiemannianCoordinates.geodesic_of_acceleration_zero (g : SmoothMetric M) {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hz : ∀ s ∈ U, covariantDerivative g γ (velocity γ) s = 0) : IsGeodesicOn g γ U := by sorry

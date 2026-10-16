-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_CoordinateMetricIsometry_along
-- name    : OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.along
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:29:03.402142+00:00
-- url     : https://prove2.me/theorems/524894fc-b3be-48cc-9b79-8ee93fbff7e5
-- title:
--   Coordinate metric isometries commute with covariant differentiation along curves
-- statement:
--   Let $M$ and $N$ be smooth ($C^\infty$) manifolds modelled on $\mathbb{R}^3$, with smooth Riemannian metrics $g$ on $M$ and $h$ on $N$, and let $c$ and $d$ be charts belonging to the atlases of $M$ and $N$ respectively; each chart is a homeomorphism from an open subset of the manifold onto an open subset of $\mathbb{R}^3$ (its *target*). In the chart $c$ the metric becomes the coordinate metric $g^c_x(u,v) = g_{c^{-1}(x)}\big(D(c^{-1})(x)u,\, D(c^{-1})(x)v\big)$ for $x$ in the target of $c$ and $u,v \in \mathbb{R}^3$, with matrix $g_{ij}(x) = g^c_x(e_i,e_j)$. Its Christoffel symbols are $\Gamma^i_{jk}(x) = \tfrac12 \sum_{l} (g(x)^{-1})_{il}\big(\partial_j g_{lk} + \partial_k g_{lj} - \partial_l g_{jk}\big)(x)$, and the *connection term* is the bilinear map $\Gamma^c_x : \mathbb{R}^3 \times \mathbb{R}^3 \to \mathbb{R}^3$, $\Gamma^c_x(u,v)^i = \sum_{j,k} \Gamma^i_{jk}(x)\, u^j v^k$. The same constructions for $h$ in the chart $d$ give $h^d_y$ and $\Gamma^d_y$.
--
--   Let $f : \mathbb{R}^3 \to \mathbb{R}^3$ and $U \subseteq \mathbb{R}^3$ form a *coordinate metric isometry* from $(g,c)$ to $(h,d)$: $U$ is open and contained in the target of $c$, $f$ maps $U$ into the target of $d$, $f$ is $C^\infty$ on $U$, the differential $Df(x)$ is surjective for every $x \in U$, and
--   $g^c_x(u,v) = h^d_{f(x)}\big(Df(x)u,\, Df(x)v\big)$ for all $x \in U$ and $u, v \in \mathbb{R}^3$.
--
--   For a curve $x : \mathbb{R} \to \mathbb{R}^3$ and a vector field $F : \mathbb{R} \to \mathbb{R}^3$ along it, the coordinate covariant derivative of $F$ along $x$ in the chart $c$ is
--   $$
--   \nabla^c_x F(s) = F'(s) + \Gamma^c_{x(s)}\big(x'(s), F(s)\big),
--   $$
--   and $\nabla^d$ is defined in the same way from $h$ in the chart $d$.
--
--   **Theorem.** Assume $c$ is in the atlas of $M$ and $d$ is in the atlas of $N$. Let $x, F : \mathbb{R} \to \mathbb{R}^3$ and $s \in \mathbb{R}$ be such that $x$ and $F$ are differentiable at $s$ and $x(s) \in U$. Let $\widetilde F(r) = Df(x(r))\,F(r)$ be the pushed-forward field along the image curve $f \circ x$. Then
--   $$
--   \nabla^d_{f \circ x} \widetilde F(s) = Df(x(s))\,\big(\nabla^c_x F(s)\big).
--   $$
--
--   Thus the image of a parallel field is parallel, and more generally covariant derivatives along curves are transported by the differential of a coordinate isometry. This is the step that makes the geodesic and Jacobi equations, written chart by chart, independent of the chart.
--
--   **Formalization Note** $\nabla^c_x F(s)$ is `alongDerivative g c x F s`, defined with Lean's `deriv`; the differentiability hypotheses on $x$ and $F$ at $s$ make these genuine derivatives. The pushed-forward field is `fun r => fderiv ℝ f (x r) (F r)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Coordinates.lean#L1180-L1199

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates

open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N}
  {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3} {f : E3 → E3}
  (P : CoordinateMetricIsometry g h c d f)

theorem OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.along (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x F : ℝ → E3} {s : ℝ}
    (hx : DifferentiableAt ℝ x s) (hF : DifferentiableAt ℝ F s)
    (hxs : x s ∈ P.domain) :
    alongDerivative h d (f ∘ x) (fun r => fderiv ℝ f (x r) (F r)) s =
      fderiv ℝ f (x s) (alongDerivative g c x F s) := by sorry

-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_CoordinateMetricIsometry_curvature
-- name    : OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.curvature
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:28:28.710362+00:00
-- url     : https://prove2.me/theorems/cd9d2d3e-431b-46b7-ae87-aacde653312a
-- title:
--   Coordinate metric isometries intertwine the curvature tensors
-- statement:
--   Let $M$ and $N$ be smooth ($C^\infty$) manifolds modelled on $\mathbb{R}^3$, with smooth Riemannian metrics $g$ on $M$ and $h$ on $N$, and let $c$ and $d$ be charts belonging to the atlases of $M$ and $N$ respectively; each chart is a homeomorphism from an open subset of the manifold onto an open subset of $\mathbb{R}^3$ (its *target*). In the chart $c$ the metric becomes the coordinate metric $g^c_x(u,v) = g_{c^{-1}(x)}\big(D(c^{-1})(x)u,\, D(c^{-1})(x)v\big)$ for $x$ in the target of $c$ and $u,v \in \mathbb{R}^3$, with matrix $g_{ij}(x) = g^c_x(e_i,e_j)$. Its Christoffel symbols are $\Gamma^i_{jk}(x) = \tfrac12 \sum_{l} (g(x)^{-1})_{il}\big(\partial_j g_{lk} + \partial_k g_{lj} - \partial_l g_{jk}\big)(x)$, and the *connection term* is the bilinear map $\Gamma^c_x : \mathbb{R}^3 \times \mathbb{R}^3 \to \mathbb{R}^3$, $\Gamma^c_x(u,v)^i = \sum_{j,k} \Gamma^i_{jk}(x)\, u^j v^k$. The same constructions for $h$ in the chart $d$ give $h^d_y$ and $\Gamma^d_y$.
--
--   Let $f : \mathbb{R}^3 \to \mathbb{R}^3$ and $U \subseteq \mathbb{R}^3$ form a *coordinate metric isometry* from $(g,c)$ to $(h,d)$: $U$ is open and contained in the target of $c$, $f$ maps $U$ into the target of $d$, $f$ is $C^\infty$ on $U$, the differential $Df(x)$ is surjective for every $x \in U$, and
--   $g^c_x(u,v) = h^d_{f(x)}\big(Df(x)u,\, Df(x)v\big)$ for all $x \in U$ and $u, v \in \mathbb{R}^3$.
--
--   The curvature term of $g$ in the chart $c$ is the trilinear map $R^c_x(u,v)w \in \mathbb{R}^3$ with components
--   $$
--   \big(R^c_x(u,v)w\big)^l = \sum_{k,i,j} R^l_{kij}(x)\, w^k u^i v^j, \qquad R^l_{kij} = \partial_i \Gamma^l_{jk} - \partial_j \Gamma^l_{ik} + \sum_{m} \big(\Gamma^l_{im}\Gamma^m_{jk} - \Gamma^l_{jm}\Gamma^m_{ik}\big),
--   $$
--   and $R^d_y$ is defined in the same way from $h$ in the chart $d$.
--
--   **Theorem.** Assume $c$ is in the atlas of $M$ and $d$ is in the atlas of $N$. Then for every $x \in U$ and all $u, v, w \in \mathbb{R}^3$, with $A = Df(x)$,
--   $$
--   R^d_{f(x)}(Au, Av)(Aw) = A\big(R^c_x(u,v)w\big).
--   $$
--
--   In words: a map that preserves the coordinate expressions of two Riemannian metrics also carries the Riemann curvature tensor of one onto that of the other. Applied to transition maps between charts (or to local isometries between manifolds), it shows that the coordinate curvature term transforms tensorially, so the Jacobi equation and sign conditions on sectional curvature written chart by chart are consistent.
--
--   **Formalization Note** The data $(U,f)$ is the structure `CoordinateMetricIsometry g h c d f`, and $R^c_x(u,v)w$ is `curvatureTerm g c x u v w`. The surjectivity of $Df(x)$ in the structure is used only through the imported connection identity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Coordinates.lean#L1150-L1179

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

theorem OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.curvature (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.domain) (u v w : E3) :
    let A := fderiv ℝ f x
    curvatureTerm h d (f x) (A u) (A v) (A w) = A (curvatureTerm g c x u v w) := by sorry

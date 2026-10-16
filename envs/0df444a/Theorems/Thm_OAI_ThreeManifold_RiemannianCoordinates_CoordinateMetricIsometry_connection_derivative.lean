-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_CoordinateMetricIsometry_connection_derivative
-- name    : OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection_derivative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:27:56.720585+00:00
-- url     : https://prove2.me/theorems/fd04255c-6c85-4a5f-83db-82d17974d886
-- title:
--   Differentiated connection identity for a coordinate metric isometry
-- statement:
--   Let $M$ and $N$ be smooth ($C^\infty$) manifolds modelled on $\mathbb{R}^3$, with smooth Riemannian metrics $g$ on $M$ and $h$ on $N$, and let $c$ and $d$ be charts belonging to the atlases of $M$ and $N$ respectively; each chart is a homeomorphism from an open subset of the manifold onto an open subset of $\mathbb{R}^3$ (its *target*). In the chart $c$ the metric becomes the coordinate metric $g^c_x(u,v) = g_{c^{-1}(x)}\big(D(c^{-1})(x)u,\, D(c^{-1})(x)v\big)$ for $x$ in the target of $c$ and $u,v \in \mathbb{R}^3$, with matrix $g_{ij}(x) = g^c_x(e_i,e_j)$. Its Christoffel symbols are $\Gamma^i_{jk}(x) = \tfrac12 \sum_{l} (g(x)^{-1})_{il}\big(\partial_j g_{lk} + \partial_k g_{lj} - \partial_l g_{jk}\big)(x)$, and the *connection term* is the bilinear map $\Gamma^c_x : \mathbb{R}^3 \times \mathbb{R}^3 \to \mathbb{R}^3$, $\Gamma^c_x(u,v)^i = \sum_{j,k} \Gamma^i_{jk}(x)\, u^j v^k$. The same constructions for $h$ in the chart $d$ give $h^d_y$ and $\Gamma^d_y$.
--
--   Let $f : \mathbb{R}^3 \to \mathbb{R}^3$ and $U \subseteq \mathbb{R}^3$ form a *coordinate metric isometry* from $(g,c)$ to $(h,d)$: $U$ is open and contained in the target of $c$, $f$ maps $U$ into the target of $d$, $f$ is $C^\infty$ on $U$, the differential $Df(x)$ is surjective for every $x \in U$, and
--   $g^c_x(u,v) = h^d_{f(x)}\big(Df(x)u,\, Df(x)v\big)$ for all $x \in U$ and $u, v \in \mathbb{R}^3$.
--
--   For $x \in U$ write $A = Df(x)$, $H = D^2f(x)$ and $K = D^3f(x)$, where $H(t,u)$ is the derivative of $y \mapsto Df(y)u$ at $x$ in direction $t$ and $K(t,u,v)$ is the derivative of $y \mapsto D^2f(y)(u,v)$ at $x$ in direction $t$. Write $D\Gamma^c_x[t]$ for the derivative at $x$ in direction $t$ of the bilinear-map-valued function $y \mapsto \Gamma^c_y$, so $D\Gamma^c_x[t](u,v)^i = \sum_{j,k,m} \partial_m \Gamma^i_{jk}(x)\, t^m u^j v^k$, and similarly $D\Gamma^d_{y}[s]$.
--
--   **Theorem.** Assume $c$ is in the atlas of $M$ and $d$ is in the atlas of $N$. Then for every $x \in U$ and all $t, u, v \in \mathbb{R}^3$,
--   $$
--   K(t,u,v) + D\Gamma^d_{f(x)}[At](Au, Av) + \Gamma^d_{f(x)}\big(H(t,u), Av\big) + \Gamma^d_{f(x)}\big(Au, H(t,v)\big) = H\big(t, \Gamma^c_x(u,v)\big) + A\big(D\Gamma^c_x[t](u,v)\big).
--   $$
--
--   This is the derivative, in the direction $t$, of the transformation law $D^2f(u,v) + \Gamma^d(Df\,u, Df\,v) = Df\,\Gamma^c(u,v)$ of the Christoffel symbols under a local isometry. It is the first-order input needed to show that coordinate isometries intertwine the curvature tensors of $g$ and $h$, which in turn makes curvature conditions and the Jacobi equation independent of the chosen chart.
--
--   **Formalization Note** The data $(U, f)$ with its properties is the structure `CoordinateMetricIsometry g h c d f` (with `P.domain` $= U$); $\Gamma^c_x$ is `connectionBilin g c x`, a continuous bilinear map, and $D\Gamma^c_x$ is the Fréchet derivative `fderiv ℝ (connectionBilin g c) x`. The inverse matrix $g(x)^{-1}$ in the Christoffel symbols is Lean's total matrix inverse; it is the genuine inverse because the coordinate metric matrix is positive definite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Coordinates.lean#L1100-L1148

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

theorem OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection_derivative (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.domain) (t u v : E3) :
    let A := fderiv ℝ f x
    let H := fderiv ℝ (fderiv ℝ f) x
    let K := fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x
    K t u v + fderiv ℝ (connectionBilin h d) (f x) (A t) (A u) (A v) +
      connectionBilin h d (f x) (H t u) (A v) + connectionBilin h d (f x) (A u) (H t v) =
      H t (connectionBilin g c x u v) + A (fderiv ℝ (connectionBilin g c) x t u v) := by sorry

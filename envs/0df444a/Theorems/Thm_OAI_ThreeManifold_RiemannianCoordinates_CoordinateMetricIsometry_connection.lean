-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_CoordinateMetricIsometry_connection
-- name    : OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:27:34.134842+00:00
-- url     : https://prove2.me/theorems/395831e7-83e0-4400-a182-2c2264e3b6c1
-- title:
--   Coordinate isometries intertwine the Christoffel symbols
-- statement:
--   Let $M$ and $N$ be smooth 3-manifolds modelled on $\mathbb{R}^3$ with smooth Riemannian metrics $g$ and $h$. For a partial homeomorphism $c:M\to\mathbb{R}^3$ and $x\in\mathbb{R}^3$, let $g^c_x(u,v)=g_{c^{-1}(x)}\bigl(d(c^{-1})_xu,\,d(c^{-1})_xv\bigr)$ be the coordinate expression of $g$. Let $\Gamma^{g,c}_x(u,v)\in\mathbb{R}^3$ be the Christoffel contraction, with components
--   $$
--   \Gamma^{g,c}_x(u,v)^i=\sum_{j,k}\Gamma^i_{jk}(x)\,u^jv^k ,\qquad
--   \Gamma^i_{jk}=\tfrac12\sum_l(G^{-1})_{il}\bigl(\partial_jG_{lk}+\partial_kG_{lj}-\partial_lG_{jk}\bigr),
--   $$
--   where $G(x)_{ij}=g^c_x(e_i,e_j)$. Define $h^d$ and $\Gamma^{h,d}$ in the same way.
--
--   A *coordinate metric isometry* from $(g,c)$ to $(h,d)$ along a map $f:\mathbb{R}^3\to\mathbb{R}^3$ consists of an open set $D$ contained in the target of $c$ such that:
--   - $f$ maps $D$ into the target of $d$;
--   - $f$ is $C^\infty$ on $D$;
--   - $Df(y)$ is surjective for every $y\in D$;
--   - $g^c_y(u,v)=h^d_{f(y)}\bigl(Df(y)u,\,Df(y)v\bigr)$ for all $y\in D$ and $u,v\in\mathbb{R}^3$.
--
--   **Theorem.** Suppose such a structure is given, $c$ is a chart of the atlas of $M$, $d$ is a chart of the atlas of $N$, and $x\in D$. Then for all $u,v\in\mathbb{R}^3$,
--   $$
--   D^2f(x)(u,v)+\Gamma^{h,d}_{f(x)}\bigl(Df(x)u,\,Df(x)v\bigr)=Df(x)\bigl(\Gamma^{g,c}_x(u,v)\bigr).
--   $$
--
--   This is the classical transformation law of Christoffel symbols under a local isometry written in coordinates. It shows that such maps carry geodesic and Jacobi equations in one chart to the corresponding equations in the other. In particular, these equations can be checked in convenient coordinates and transported along isometries.
--
--   **Formalization Note** $D^2f(x)(u,v)$ is `fderiv ℝ (fderiv ℝ f) x u v`, the derivative in direction $u$ of $Df$ applied to $v$. The coordinate metric $g^c_x$ is `chartBilin g c x`, defined with Mathlib's manifold derivative of $c^{-1}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Coordinates.lean#L1061-L1090

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

theorem OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.connection (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.domain) (u v : E3) :
    fderiv ℝ (fderiv ℝ f) x u v +
        connectionTerm h d (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) =
      fderiv ℝ f x (connectionTerm g c x u v) := by sorry

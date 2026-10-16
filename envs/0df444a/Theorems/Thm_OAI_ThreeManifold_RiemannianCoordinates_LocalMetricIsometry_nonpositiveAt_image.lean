-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_nonpositiveAt_image
-- name    : OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.nonpositiveAt_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:53:42.254397+00:00
-- url     : https://prove2.me/theorems/7acd6c7d-e3ee-48e9-960c-04fa696e8643
-- title:
--   Pointwise nonpositive curvature is transported forward by local metric isometries
-- statement:
--   Let $M$ and $N$ be smooth ($C^\infty$) manifolds modelled on $\mathbb{R}^3$, carrying smooth Riemannian metrics $g$ and $h$ respectively. For an atlas chart $c$ of $M$ and a point $x$ of its image, write
--   $\langle u,v\rangle^{g,c}_x = g_{c^{-1}(x)}\big(Dc^{-1}(x)\,u,\ Dc^{-1}(x)\,v\big)$ for the metric in the coordinates of $c$, and $R^{g,c}_x(u,v)w\in\mathbb{R}^3$ for the coordinate curvature term, whose $l$-th component is $\sum_{i,j,k} R^l_{kij}(x)\,w^k u^i v^j$ with
--   $R^l_{kij} = \partial_i\Gamma^l_{jk} - \partial_j\Gamma^l_{ik} + \sum_a\big(\Gamma^l_{ia}\Gamma^a_{jk} - \Gamma^l_{ja}\Gamma^a_{ik}\big)$, where $\Gamma^l_{ij}$ are the Christoffel symbols of $g$ in the chart $c$. The same notation is used for $h$ on $N$. We say that $g$ is *nonpositively curved at* $p\in M$ if for every atlas chart $c$ whose domain contains $p$ and all $u,v\in\mathbb{R}^3$,
--   $$
--   \big\langle R^{g,c}_{c(p)}(u,v)v,\ u\big\rangle^{g,c}_{c(p)} \le 0 .
--   $$
--
--   A *local metric isometry* from $(M,g)$ to $(N,h)$ along a map $f : M\to N$ is an open set $D\subseteq M$ such that $f$ is $C^\infty$ on $D$ and $g_p(u,v) = h_{f(p)}(Df_p\,u,\ Df_p\,v)$ for every $p\in D$ and all tangent vectors $u,v$ at $p$.
--
--   **Theorem.** Let $f$ be a local metric isometry from $(M,g)$ to $(N,h)$ with domain $D$, and let $p\in D$. If $g$ is nonpositively curved at $p$, then $h$ is nonpositively curved at $f(p)$: for every atlas chart $d$ of $N$ whose domain contains $f(p)$ and all $u,v\in\mathbb{R}^3$,
--   $$
--   \big\langle R^{h,d}_{d(f(p))}(u,v)v,\ u\big\rangle^{h,d}_{d(f(p))} \le 0 .
--   $$
--
--   The quantity $\langle R(u,v)v,u\rangle$ is the chartwise form of the sectional-curvature condition used in the definition of nonpositive sectional curvature, so the result says that this pointwise curvature sign can be moved forward along any local isometry, for instance from a manifold to a coordinate model of part of it. No injectivity or surjectivity of $f$ is assumed.
--
--   **Formalization Note** The pointwise condition is `NonpositiveAt`, the local isometry is the structure `LocalMetricIsometry g h f` with field `domain`, and the coordinate inner product is `chartBilin`. The tangent spaces of $M$ and $N$ are identified with $\mathbb{R}^3$ through Mathlib's model-space convention.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Curvature.lean#L598-L614

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
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

theorem OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.nonpositiveAt_image {g : SmoothMetric M} {h : SmoothMetric N}
    {f : M → N} (P : LocalMetricIsometry g h f) {p : M} (hp : p ∈ P.domain)
    (hn : NonpositiveAt g p) : NonpositiveAt h (f p) := by sorry

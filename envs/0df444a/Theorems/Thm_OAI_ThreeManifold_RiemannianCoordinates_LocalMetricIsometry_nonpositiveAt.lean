-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_nonpositiveAt
-- name    : OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.nonpositiveAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:52:36.805649+00:00
-- url     : https://prove2.me/theorems/71695ac7-4e91-4427-a6ef-df61037c8bef
-- title:
--   Nonpositive curvature pulls back along a local isometry
-- statement:
--   Let $M$ and $N$ be smooth ($C^\infty$) manifolds modelled on $\mathbb{R}^3$, with tangent spaces identified with $\mathbb{R}^3$ through the model, and let $g$ and $h$ be smooth Riemannian metrics on $M$ and $N$. For a chart $c$ in the atlas, $dc_p : T_pM \to \mathbb{R}^3$ is its derivative at $p$ and $c^{-1}$ its inverse on the chart target. Let $f : M \to N$ be a map and let $\mathcal{P}$ be a local metric isometry along $f$: an open set $\mathcal{D} \subseteq M$ (its domain) on which $f$ is $C^\infty$ and
--   $$
--   g_p(u, w) = h_{f(p)}\big(df_p\, u,\ df_p\, w\big) \qquad (p \in \mathcal{D},\ u, w \in T_pM).
--   $$
--
--   For an atlas chart $c$ of $M$ and $y$ in its target, let $\langle a, b\rangle_{c,y} = g_{c^{-1}(y)}\big(d(c^{-1})_y\, a,\ d(c^{-1})_y\, b\big)$ be the coordinate metric on $\mathbb{R}^3$, $\Gamma^l_{ij}(y)$ its Christoffel symbols, and $\mathcal{R}_c(y)(u, v)w \in \mathbb{R}^3$ the coordinate curvature term with components
--   $$
--   \mathcal{R}_c(y)(u,v)w^{\,l} = \sum_{k,i,j} R^l_{kij}(y)\, w^k u^i v^j, \qquad R^l_{kij} = \partial_i \Gamma^l_{jk} - \partial_j \Gamma^l_{ik} + \sum_a \big(\Gamma^l_{ia}\Gamma^a_{jk} - \Gamma^l_{ja}\Gamma^a_{ik}\big).
--   $$
--   The metric $g$ is *nonpositively curved at* $p \in M$ if for every atlas chart $c$ whose source contains $p$ and all $u, v \in \mathbb{R}^3$,
--   $$
--   \big\langle \mathcal{R}_c(c(p))(u, v)v,\ u\big\rangle_{c, c(p)} \le 0 ,
--   $$
--   and similarly for $h$ on $N$.
--
--   **Theorem.** If $p \in \mathcal{D}$ and $h$ is nonpositively curved at $f(p)$, then $g$ is nonpositively curved at $p$.
--
--   This is the pointwise curvature comparison through a local isometry: curvature conditions verified on a model (for instance on a covering space or a locally isometric piece) hold on the manifold itself, which is how regions of nonpositive curvature are certified.
--
--   **Formalization Note** The predicate is `NonpositiveAt`, the coordinate metric is `chartBilin`, and the coordinate curvature term is `curvatureTerm`, with the same sign conventions as the nonpositive sectional curvature condition in the main statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Curvature.lean#L280-L299

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

open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)

theorem OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.nonpositiveAt (p : M) (hp : p ∈ P.domain) (hn : NonpositiveAt h (f p)) :
    NonpositiveAt g p := by sorry

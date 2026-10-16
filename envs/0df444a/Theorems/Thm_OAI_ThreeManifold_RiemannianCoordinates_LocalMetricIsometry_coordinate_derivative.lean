-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_coordinate_derivative
-- name    : OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.coordinate_derivative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:48:44.222974+00:00
-- url     : https://prove2.me/theorems/3e120423-258d-4837-9d82-5f7f55c89776
-- title:
--   Chart expression of the differential of a local isometry
-- statement:
--   Let $M$ and $N$ be smooth ($C^\infty$) manifolds modelled on $\mathbb{R}^3$, with tangent spaces identified with $\mathbb{R}^3$ through the model, and let $g$ and $h$ be smooth Riemannian metrics on $M$ and $N$. For a chart $c$ in the atlas, $dc_p : T_pM \to \mathbb{R}^3$ is its derivative at $p$ and $c^{-1}$ its inverse on the chart target. Let $f : M \to N$ be a map and let $\mathcal{P}$ be a local metric isometry along $f$: an open set $\mathcal{D} \subseteq M$ (its domain) on which $f$ is $C^\infty$ and
--   $$
--   g_p(u, w) = h_{f(p)}\big(df_p\, u,\ df_p\, w\big) \qquad (p \in \mathcal{D},\ u, w \in T_pM).
--   $$
--
--   **Theorem.** Let $c$ be a chart in the atlas of $M$ and $d$ a chart in the atlas of $N$, and let $p \in \mathcal{D}$ with $p$ in the source of $c$ and $f(p)$ in the source of $d$. Then for every $u \in T_pM$,
--   $$
--   dd_{f(p)}\big(df_p\, u\big) = D\big(d\circ f\circ c^{-1}\big)\big(c(p)\big)\,\big(dc_p\, u\big),
--   $$
--   where $D$ denotes the ordinary (Fréchet) derivative of the map $d\circ f\circ c^{-1}$ between open subsets of $\mathbb{R}^3$.
--
--   So the differential of $f$, read in the charts $c$ and $d$, is the Jacobian of the coordinate representation of $f$. This is the basic translation step used to transport vector fields, covariant derivatives and curvature along a local isometry by computing in coordinates.
--
--   **Formalization Note** Only the smoothness of $f$ on $\mathcal{D}$ is used; the metric condition plays no role here. The structure $\mathcal{P}$ is `LocalMetricIsometry g h f` and $\mathcal{D}$ is `P.domain`; derivatives on manifolds are `mfderiv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Curvature.lean#L105-L135

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

theorem OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.coordinate_derivative {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {p : M}
    (hp : p ∈ P.domain) (hpc : p ∈ c.source) (hpd : f p ∈ d.source) (u : TangentSpace I3 p) :
    mfderiv I3 I3 d (f p) (mfderiv I3 I3 f p u) =
      fderiv ℝ (d ∘ f ∘ c.symm) (c p) (mfderiv I3 I3 c p u) := by sorry

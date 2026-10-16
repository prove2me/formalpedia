-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_finite_neck_neighborhood
-- name    : OAI.ThreeManifold.CompactMetric.finite_neck_neighborhood
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:24:48.147596+00:00
-- url     : https://prove2.me/theorems/9194e28d-4387-4a0b-b3d4-f8960c14d236
-- title:
--   A geodesic segment crossing the open neck stays in the extended neck on an open interval around it
-- statement:
--   Let $\Sigma=\mathbb{H}/\Gamma$ be the cusped hyperbolic surface of the construction, with its height function $\operatorname{ht}:\Sigma\to\mathbb{R}$, $\operatorname{ht}(\pi(z))=\log\max_{g\in\Gamma}\operatorname{Im}(g z)$, so that for $a>1$ the cusp region $\{\operatorname{Im} z>a\}$ projects onto $\{\operatorname{ht}>\log a\}$. The *piece* is $P=\{x\in\Sigma:\operatorname{ht}(x)<\log 8\}\times\mathbb{R}/6\mathbb{Z}$, and its *collar* is $\mathcal{C}=\{(x,\theta)\in P:\operatorname{ht}(x)>\log 2\}$. The 3-manifold $M$ is obtained from two copies of $P$, with inclusions $\iota_0,\iota_1:P\to M$, by identifying $\iota_0(w)$ with $\iota_1(\phi(w))$ for $w\in\mathcal{C}$, where $\phi$ is the fixed gluing homeomorphism of the collar. The *open neck* is $\mathcal{N}=\iota_0(\mathcal{C})$, which equals $\iota_1(\mathcal{C})$. With the *extended piece* $P'=\{(x,\theta)\in P:\operatorname{ht}(x)>1/2\}$, the *extended neck* is $\mathcal{N}'=\iota_0(P')\cup\iota_1(P')$.
--
--   For $\delta\in(0,\tfrac12]$, let $g_\delta$ be the smooth Riemannian metric on $M$ constructed in this family. A geodesic of $g_\delta$ on an open set $U\subseteq\mathbb{R}$ is a curve that is $C^\infty$ on $U$ and satisfies the geodesic equation in every chart. A set $W\subseteq\mathbb{R}$ is *order-connected* if $s,t\in W$ and $s\le r\le t$ imply $r\in W$.
--
--   **Theorem.** Let $\delta\in(0,\tfrac12]$, let $U\subseteq\mathbb{R}$ be open, and let $\gamma:\mathbb{R}\to M$ be a geodesic of $g_\delta$ on $U$. Let $a<b$ with $[a,b]\subseteq U$ and $\gamma(s)\in\mathcal{N}$ for all $s\in(a,b)$. Then there is an open, order-connected set $W\subseteq\mathbb{R}$ with
--   $$
--   [a,b]\subseteq W\subseteq U\qquad\text{and}\qquad \gamma(W)\subseteq\mathcal{N}'.
--   $$
--
--   So a geodesic segment whose interior runs through the open neck can be thickened to an open time interval during which the geodesic stays in the extended neck, where the neck coordinates (and the local isometry to the warped model) are available. Note that the endpoints $\gamma(a),\gamma(b)$ themselves need not lie in the open neck.
--
--   **Formalization Note** In Lean, $M$ is `GluedConstruction.Manifold`, $g_\delta$ is `realCompactMetric hδ`, $\mathcal{N}$ is `openNeck` and $\mathcal{N}'$ is `extendedNeck`. Order-connectedness is Mathlib's `OrdConnected`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L672-L692

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

open OAI OAI.ThreeManifold OAI.ThreeManifold.CompactMetric
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_4

theorem OAI.ThreeManifold.CompactMetric.finite_neck_neighborhood {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ : ℝ → GluedConstruction.Manifold}
    (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ U) (hr : ∀ s ∈ Ioo a b, γ s ∈ openNeck) :
    ∃ W : Set ℝ, IsOpen W ∧ OrdConnected W ∧ Icc a b ⊆ W ∧ W ⊆ U ∧
      MapsTo γ W extendedNeck := by sorry

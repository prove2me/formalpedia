-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_finite_neck_height_boundary
-- name    : OAI.ThreeManifold.CompactMetric.finite_neck_height_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:26:05.094497+00:00
-- url     : https://prove2.me/theorems/842865e1-c6da-4241-a503-259facb7f0d7
-- title:
--   A geodesic arc inside the neck has neck height in $[0,1]$ and leaves only through the ends
-- statement:
--   Let $M$ be the closed three-manifold of the main construction: two copies of a piece $X$ (the product of the open core $\{h_\Sigma<\log 8\}$ of a cusped hyperbolic surface $\Sigma$ with height function $h_\Sigma$, times a circle) glued to each other along their collars $\{h_\Sigma>\log 2\}$. Fix $\delta\in(0,\tfrac12]$ and let $g_\delta$ be the smooth Riemannian metric on $M$ obtained from the neck of parameter $\delta$. Let $N\subset M$ be the open neck, i.e. the image of the collar of the first copy, and let $\nu_\delta : M\to\mathbb{R}\times(\mathbb{R}/6\mathbb{Z})^2$ be the neck-position map; write $h(q)\in\mathbb{R}$ for the first component of $\nu_\delta(q)$, the normalized coordinate along the neck.
--
--   Let $U\subseteq\mathbb{R}$ be open and let $\gamma:\mathbb{R}\to M$ be a geodesic of $g_\delta$ on $U$: $\gamma$ is $C^\infty$ on $U$, and in every chart of the atlas of $M$ its coordinate expression $x(s)$ satisfies $\ddot x^i+\Gamma^i_{jk}(x)\dot x^j\dot x^k=0$ at every $s\in U$ with $\gamma(s)$ in the chart domain, where $\Gamma^i_{jk}$ are the Christoffel symbols of $g_\delta$ in that chart. Let $a<b$ with $[a,b]\subseteq U$, and suppose $\gamma(s)\in N$ for every $s\in(a,b)$. Then:
--
--   1. $h(\gamma(s))\in[0,1]$ for every $s\in[a,b]$;
--   2. if $\gamma(a)\notin N$, then $h(\gamma(a))\in\{0,1\}$;
--   3. if $\gamma(b)\notin N$, then $h(\gamma(b))\in\{0,1\}$.
--
--   In one line,
--   $$
--   h(\gamma([a,b]))\subseteq[0,1],\qquad \gamma(a)\notin N\Rightarrow h(\gamma(a))\in\{0,1\},\qquad \gamma(b)\notin N\Rightarrow h(\gamma(b))\in\{0,1\}.
--   $$
--
--   Thus a geodesic arc whose interior runs inside the neck can only enter or leave the neck through one of its two ends, at neck height $0$ or $1$. This supplies the boundary values for the height function $s\mapsto h(\gamma(s))$ of a neck passage, which is then analysed through the one-dimensional height equation.
--
--   **Formalization Note** $M$ is `GluedConstruction.Manifold`, $g_\delta$ is `realCompactMetric hδ` (the glued metric read in the real three-dimensional charts), $N$ is `openNeck` and $h$ is `(neckPosition δ ·).1`. Geodesics are expressed by `IsGeodesicOn`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L694-L720

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

theorem OAI.ThreeManifold.CompactMetric.finite_neck_height_boundary {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ : ℝ → GluedConstruction.Manifold}
    (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ U) (hr : ∀ s ∈ Ioo a b, γ s ∈ openNeck) :
    (∀ s ∈ Icc a b, (neckPosition δ (γ s)).1 ∈ Icc (0:ℝ) 1) ∧
    (γ a ∉ openNeck → (neckPosition δ (γ a)).1 = 0 ∨ (neckPosition δ (γ a)).1 = 1) ∧
    (γ b ∉ openNeck → (neckPosition δ (γ b)).1 = 0 ∨ (neckPosition δ (γ b)).1 = 1) := by sorry

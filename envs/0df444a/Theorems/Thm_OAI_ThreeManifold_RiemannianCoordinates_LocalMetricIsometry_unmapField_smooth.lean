-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_unmapField_smooth
-- name    : OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.unmapField_smooth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:19:03.615354+00:00
-- url     : https://prove2.me/theorems/3fca04a5-b16b-44dd-adbc-210c6555fb0c
-- title:
--   Pulling back a smooth vector field along a curve through a local metric isometry preserves smoothness
-- statement:
--   Let $M$ and $N$ be smooth manifolds modelled on $\mathbb{R}^3$ with smooth Riemannian metrics $g$ and $h$, and let $f:M\to N$ be a *local metric isometry* with domain $D$. That is, $D\subseteq M$ is open, $f$ is $C^\infty$ on $D$, and $g_p(u,v)=h_{f(p)}(Df_p\,u,Df_p\,v)$ for all $p\in D$ and tangent vectors $u,v$ at $p$. In particular $Df_p$ is invertible for $p\in D$.
--
--   For a curve $\sigma:\mathbb{R}\to M$, a *vector field along $\sigma$* assigns to each $s$ a tangent vector $J(s)$ at $\sigma(s)$. It is *smooth on* $U\subseteq\mathbb{R}$ if for every atlas chart $c$ the coordinate function $s\mapsto Dc_{\sigma(s)}J(s)\in\mathbb{R}^3$ is $C^\infty$ on $U\cap\sigma^{-1}(\mathrm{dom}\,c)$. Given a curve $\gamma$ in $M$ and a field $J$ along $f\circ\gamma$, the *pulled-back field* along $\gamma$ is
--   $$
--   (f^{*}J)(s)=\big(Df_{\gamma(s)}\big)^{-1}J(s).
--   $$
--
--   **Theorem.** Let $U\subseteq\mathbb{R}$ be open, let $\gamma:\mathbb{R}\to M$ be $C^\infty$ on $U$ with $\gamma(U)\subseteq D$, and let $J$ be a vector field along $f\circ\gamma$ that is smooth on $U$. Then the pulled-back field $f^{*}J$ is a smooth vector field along $\gamma$ on $U$.
--
--   Together with the forward direction (pushing a field along $\gamma$ forward by $Df$), this lets vector fields along curves, such as Jacobi fields, be transferred in both directions between a manifold and a locally isometric model.
--
--   **Formalization Note** The pulled-back field is `P.unmapField γ J`. It uses `ContinuousLinearMap.inverse`, which returns $0$ for non-invertible maps, but on $D$ the differential is invertible, so this convention plays no role under the hypothesis $\gamma(U)\subseteq D$. Smoothness along a curve is `SmoothFieldOn`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L441-L461

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

open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)

theorem OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.unmapField_smooth {γ : ℝ → M} {J : ∀ s, TangentSpace I3 ((f ∘ γ) s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hJ : SmoothFieldOn (f ∘ γ) J U) : SmoothFieldOn γ (P.unmapField γ J) U := by sorry

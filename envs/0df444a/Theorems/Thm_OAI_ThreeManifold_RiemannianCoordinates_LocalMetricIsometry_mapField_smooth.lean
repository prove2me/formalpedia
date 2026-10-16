-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_mapField_smooth
-- name    : OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.mapField_smooth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:49:13.659098+00:00
-- url     : https://prove2.me/theorems/f2942a45-a621-4941-bcde-c43a3102da7b
-- title:
--   A local isometry pushes smooth vector fields along curves to smooth vector fields
-- statement:
--   Let $M$ and $N$ be smooth ($C^\infty$) manifolds modelled on $\mathbb{R}^3$, with tangent spaces identified with $\mathbb{R}^3$ through the model, and let $g$ and $h$ be smooth Riemannian metrics on $M$ and $N$. For a chart $c$ in the atlas, $dc_p : T_pM \to \mathbb{R}^3$ is its derivative at $p$ and $c^{-1}$ its inverse on the chart target. Let $f : M \to N$ be a map and let $\mathcal{P}$ be a local metric isometry along $f$: an open set $\mathcal{D} \subseteq M$ (its domain) on which $f$ is $C^\infty$ and
--   $$
--   g_p(u, w) = h_{f(p)}\big(df_p\, u,\ df_p\, w\big) \qquad (p \in \mathcal{D},\ u, w \in T_pM).
--   $$
--
--   For a curve $\gamma : \mathbb{R} \to M$ and a vector field $J$ along it ($J(s) \in T_{\gamma(s)}M$), write $\hat J_c(s) = dc_{\gamma(s)} J(s)$ for its coordinates in a chart $c$. The covariant derivative is computed in the preferred chart $c$ at $\gamma(s)$: with $x = c\circ\gamma$,
--   $$
--   \frac{D J}{ds}(s) = d(c^{-1})_{x(s)}\Big(\hat J_c'(s) + \Gamma_c\big(x(s)\big)\big(x'(s), \hat J_c(s)\big)\Big),
--   $$
--   where $\Gamma_c(y)(u, w)^i = \sum_{j,k} \Gamma^i_{jk}(y)\, u^j w^k$ and $\Gamma^i_{jk}$ are the Christoffel symbols of the coordinate metric matrix $g_{ij}(y) = g(\partial_i, \partial_j)$ of $c$. The field $J$ is smooth along $\gamma$ on $U \subseteq \mathbb{R}$ if for every atlas chart $c$ the map $s \mapsto \hat J_c(s)$ is $C^\infty$ on $U \cap \gamma^{-1}(\operatorname{source} c)$. The pushed-forward field along $f\circ\gamma$ is $(f_*J)(s) = df_{\gamma(s)} J(s)$.
--
--   **Theorem.** Let $U \subseteq \mathbb{R}$ be open, let $\gamma : \mathbb{R} \to M$ be $C^\infty$ on $U$ with $\gamma(U) \subseteq \mathcal{D}$, and let $J$ be a vector field along $\gamma$ that is smooth along $\gamma$ on $U$. Then the pushed-forward field is smooth along $f\circ\gamma$ on $U$:
--   $$
--   J \ \text{smooth along } \gamma \text{ on } U \ \Longrightarrow\ f_*J \ \text{smooth along } f\circ\gamma \text{ on } U .
--   $$
--
--   This regularity statement is needed so that covariant derivatives of pushed-forward fields along the image curve are defined and can be computed in coordinates; it is used when Jacobi fields and index forms are transferred through a local isometry.
--
--   **Formalization Note** Smoothness along a curve is `SmoothFieldOn`, the pushed-forward field is `P.mapField γ J`, and smoothness of $\gamma$ is `ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Curvature.lean#L151-L176

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

theorem OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.mapField_smooth {γ : ℝ → M} {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hJ : SmoothFieldOn γ J U) : SmoothFieldOn (f ∘ γ) (P.mapField γ J) U := by sorry

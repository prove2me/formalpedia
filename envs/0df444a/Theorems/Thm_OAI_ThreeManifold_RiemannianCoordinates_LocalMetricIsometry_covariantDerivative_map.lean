-- Prove2me | Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_covariantDerivative_map
-- name    : OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.covariantDerivative_map
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:52:03.905922+00:00
-- url     : https://prove2.me/theorems/2e4d424e-2ed8-464a-86a5-d65e6705aa38
-- title:
--   Local isometries commute with covariant differentiation along curves
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
--   **Theorem.** Let $U \subseteq \mathbb{R}$ be open, let $\gamma : \mathbb{R} \to M$ be $C^\infty$ on $U$ with $\gamma(U) \subseteq \mathcal{D}$, let $J$ be a vector field along $\gamma$ that is smooth along $\gamma$ on $U$, and let $s \in U$. Then
--   $$
--   \frac{D^{h}(f_*J)}{ds}(s) = df_{\gamma(s)}\Big(\frac{D^{g} J}{ds}(s)\Big),
--   $$
--   where $D^g/ds$ is the covariant derivative along $\gamma$ for $g$ and $D^h/ds$ the covariant derivative along $f\circ\gamma$ for $h$.
--
--   Together with the corresponding statement for curvature, this shows that index forms and Jacobi fields along a curve in $\mathcal{D}$ correspond exactly to those along its image, so properties such as the absence of conjugate points can be transferred through local isometries (for example from a covering or a model space).
--
--   **Formalization Note** Smoothness along a curve is `SmoothFieldOn`, the pushed-forward field is `P.mapField γ J`, and `covariantDerivative` is defined using the preferred chart `chartAt` at $\gamma(s)$ as described above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Curvature.lean#L208-L237

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

theorem OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.covariantDerivative_map {γ : ℝ → M} {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hJ : SmoothFieldOn γ J U) {s : ℝ} (hs : s ∈ U) :
    covariantDerivative h (f ∘ γ) (P.mapField γ J) s =
      mfderiv I3 I3 f (γ s) (covariantDerivative g γ J s) := by sorry

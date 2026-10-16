-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_monotone_index
-- name    : OAI.ThreeManifold.CompactMetric.framed_monotone_index
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:03:26.635272+00:00
-- url     : https://prove2.me/theorems/989fd41a-27f1-4bcd-b22e-755cdfa7040b
-- title:
--   Nonnegative index along a monotone passage through the framed neck
-- statement:
--   This result handles passages through the neck along which the height of the geodesic is strictly monotone (no turning point).
--
--   **Setting.** Fix $\delta\in(0,\tfrac12]$ and a frame $F\in\{\mathrm L,\mathrm R\}$. Points and vectors of $\mathbb R^3$ are split as $x=(x_0,\bar x)$ with height $x_0\in\mathbb R$ and torus part $\bar x=(x_1,x_2)\in\mathbb R^2$. Let $a(u)=e^{-1/(2/3-u)}$ for $u<\tfrac23$ and $a(u)=0$ otherwise, $A(t)=\int_0^t a(y)\,dy$, and $\chi(t)=\psi\big(6(t-\tfrac5{12})\big)$, where $\psi$ is the standard smooth transition function ($\psi=0$ on $(-\infty,0]$, $\psi=1$ on $[1,\infty)$). The two cometrics are the symmetric $2\times2$ matrices
--   $$P^{\mathrm L}(t)=\begin{pmatrix} d_1(t)+d_2(t)\sigma(t)^2 & d_2(t)\sigma(t)\\ d_2(t)\sigma(t) & d_2(t)\end{pmatrix},\qquad P^{\mathrm R}(t)=K\,P^{\mathrm L}(1-t)\,K^{\mathsf T},$$
--   where $d_1(t)=1+\delta A(t)$, $d_2(t)=1+\delta A(1-t)$, $\sigma(t)=\delta^2\chi(t)$ and $K=\begin{pmatrix}0&1\\1&-\delta^2\end{pmatrix}$. Write $P=P^F$, $Q(t)=P(t)^{-1}$, and $Q',Q''$ for the derivatives of $t\mapsto Q(t)$. The framed neck metric $g=g^F_\delta$ is a smooth Riemannian metric on $\mathbb R^3$ (for $F=\mathrm L$ the normalized neck metric, for $F=\mathrm R$ its pullback under the affine map $y\mapsto(1-y_0,\ \delta^2y_1+y_2,\ y_1)$) which on the slab $-\tfrac14<x_0<\tfrac54$ has the block form
--   $$g_x(u,w)=u_0w_0+\bar u^{\mathsf T}Q(x_0)\,\bar w .$$
--
--   Here $\mathbb R^3$ carries its single identity chart, so tangent vectors are elements of $\mathbb R^3$. A curve $\gamma:\mathbb R\to\mathbb R^3$ is a geodesic of $g$ on an open set $U\subseteq\mathbb R$ if it is $C^\infty$ on $U$ and $\ddot\gamma(s)+\Gamma_{\gamma(s)}(\dot\gamma(s),\dot\gamma(s))=0$ for all $s\in U$, where $\Gamma_x(u,w)^i=\sum_{j,k}\Gamma^i_{jk}(x)u^jw^k$ is formed with the Christoffel symbols of $g$. A vector field along $\gamma$ is a map $J:\mathbb R\to\mathbb R^3$, called smooth on $U$ if it is $C^\infty$ there; its covariant derivative is $\nabla_sJ=\dot J+\Gamma_{\gamma}(\dot\gamma,J)$ and its index density is
--   $$\mathcal I(s)=g_{\gamma(s)}\big(\nabla_sJ,\nabla_sJ\big)-g_{\gamma(s)}\big(R(J,\dot\gamma)\dot\gamma,\,J\big),$$
--   where $R$ is the Riemann curvature tensor of $g$ with $R(\partial_i,\partial_j)\partial_k=\nabla_i\nabla_j\partial_k-\nabla_j\nabla_i\partial_k$ (so the Jacobi equation reads $\nabla_s^2J+R(J,\dot\gamma)\dot\gamma=0$). Thus $\int_a^b\mathcal I\,ds$ is the index form of $J$ on $[a,b]$.
--
--   **Statement.** Let $U\subseteq\mathbb R$ be open, $a<b$ with $[a,b]\subseteq U$, $\gamma$ a geodesic of $g=g^F_\delta$ on $U$, $J$ a vector field along $\gamma$ that is smooth on $U$, and $p\in\mathbb R^2$. Assume:
--
--   1. (conserved momentum) $Q(\gamma_0(s))\,\dot{\bar\gamma}(s)=p$ for all $s\in[a,b]$;
--   2. (unit speed) $g_{\gamma(s)}(\dot\gamma(s),\dot\gamma(s))=1$ for all $s\in[a,b]$;
--   3. (passage) $\gamma_0(s)\in[0,1]$ for $s\in[a,b]$ and $\gamma_0(s)\in(0,1)$ for $s\in(a,b)$;
--   4. (endpoints) at each endpoint $e\in\{a,b\}$, either $\gamma_0(e)\in\{0,1\}$ or $J$ vanishes identically on a neighbourhood of $e$;
--   5. (no turning point) $\dot\gamma_0(s)\neq0$ for all $s\in(a,b)$.
--
--   Then
--   $$\int_a^b\mathcal I(s)\,ds\;\ge\;0 .$$
--
--   No smallness condition on $\delta$ beyond $\delta\in(0,\tfrac12]$ is needed. Together with the estimate for returning passages, this covers every unit-speed passage of a geodesic through the neck that starts on its boundary.
--
--   **Formalization Note** The frame is a Boolean `right`; $Q$ is `metricInverse right δ` and $\mathcal I$ is `indexPairDensity (framedNeck right hδ) γ J J`. The endpoint alternatives are written `(γ a 0 = 0 ∨ γ a 0 = 1) ∨ J =ᶠ[𝓝 a] 0` and similarly at $b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean#L1153-L1225

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
import Definitions.Def_OAI_Geometry_ConjugatePoints_NoConjugatePoints

open OAI OAI.ThreeManifold OAI.ThreeManifold.CompactMetric
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage PassageDynamics

theorem OAI.ThreeManifold.CompactMetric.framed_monotone_index (right : Bool) {δ a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {U : Set ℝ} (hU : IsOpen U) (hab : a < b) (hsub : Icc a b ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : SmoothFieldOn γ J U) {p : TVec}
    (hp : ∀ s ∈ Icc a b, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p)
    (hrc : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo a b, γ s 0 ∈ Ioo (0:ℝ) 1)
    (ha : (γ a 0 = 0 ∨ γ a 0 = 1) ∨ J =ᶠ[𝓝 a] 0)
    (hb : (γ b 0 = 0 ∨ γ b 0 = 1) ∨ J =ᶠ[𝓝 b] 0)
    (hn : ∀ s ∈ Ioo a b, deriv γ s 0 ≠ 0)
    (hunit : ∀ s ∈ Icc a b,
      (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by sorry

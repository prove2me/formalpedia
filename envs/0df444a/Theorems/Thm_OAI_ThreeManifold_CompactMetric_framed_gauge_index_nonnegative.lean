-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_gauge_index_nonnegative
-- name    : OAI.ThreeManifold.CompactMetric.framed_gauge_index_nonnegative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:01:29.659168+00:00
-- url     : https://prove2.me/theorems/db269a32-8ac4-42ce-8afa-4d402a46e4d9
-- title:
--   Gauge criterion for nonnegative index along framed neck geodesics
-- statement:
--   This criterion gives nonnegativity of the index form for a field whose vertical component can be removed by adding a multiple of the velocity.
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
--   For a field $W$ along $\gamma$ write $t=\gamma_0(s)$, $T=\dot\gamma(s)$, $V=W(s)$ and define the boundary term
--   $$\beta_W(s)=-\tfrac12\,T_0\,\bar V^{\mathsf T}Q'(t)\,\bar V+V_0\,\bar T^{\mathsf T}Q'(t)\,\bar V .$$
--
--   **Statement.** Let $U\subseteq\mathbb R$ be open, $\gamma$ a geodesic of $g=g^F_\delta$ on $U$, $J:\mathbb R\to\mathbb R^3$ and $h:\mathbb R\to\mathbb R$ maps that are $C^\infty$ on $U$, and put $W=J+h\,\dot\gamma$. Assume $W_0(s)=0$ for all $s\in U$. Let $a\le b$ with $[a,b]\subseteq U$, and assume $\gamma_0(s)\in[0,1]$ and $g_{\gamma(s)}(\dot\gamma(s),\dot\gamma(s))=1$ for all $s\in[a,b]$, and
--   $$\beta_W(b)\le\beta_W(a).$$
--   Then
--   $$\int_a^b\mathcal I(s)\,ds\;\ge\;0,$$
--   where $\mathcal I$ is the index density of $J$ along $\gamma$.
--
--   Adding a multiple of the velocity does not change the normal part of the index density, so the sign question for $J$ reduces to the horizontal field $W$. Where the vertical speed $\dot\gamma_0$ is nonzero one can take $h=-J_0/\dot\gamma_0$; this is how monotone passages through the neck are handled.
--
--   **Formalization Note** The hypothesis $W_0=0$ is `(J s + h s • deriv γ s) 0 = 0`; $\beta_W$ is `boundaryTerm (deriv (metricInverse right δ) (γ s 0)) (splitVector (deriv γ s)) (splitVector (J s + h s • deriv γ s))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean#L833-L897

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
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck

theorem OAI.ThreeManifold.CompactMetric.framed_gauge_index_nonnegative (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ J : ℝ → E3} {h : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn (framedNeck right hδ) γ U) (hJ : ContDiffOn ℝ ∞ J U)
    (hh : ContDiffOn ℝ ∞ h U)
    (hzero : ∀ s ∈ U, (J s + h s • deriv γ s) 0 = 0)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (htr : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hunit : ∀ s ∈ Icc a b, (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1)
    (hboundary : boundaryTerm (deriv (metricInverse right δ) (γ b 0))
      (splitVector (deriv γ b)) (splitVector (J b + h b • deriv γ b)) ≤
      boundaryTerm (deriv (metricInverse right δ) (γ a 0)) (splitVector (deriv γ a))
        (splitVector (J a + h a • deriv γ a))) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by sorry

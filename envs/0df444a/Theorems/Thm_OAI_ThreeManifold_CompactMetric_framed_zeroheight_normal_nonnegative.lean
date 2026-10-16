-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_zeroheight_normal_nonnegative
-- name    : OAI.ThreeManifold.CompactMetric.framed_zeroheight_normal_nonnegative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:00:41.679826+00:00
-- url     : https://prove2.me/theorems/d42f2678-7387-40d7-a596-7520c7ed7c44
-- title:
--   Normal index of a horizontal field in the framed neck is nonnegative under a boundary sign condition
-- statement:
--   This result controls the normal part of the index form for fields along a framed-neck geodesic that have no vertical (height) component.
--
--   **Setting.** Fix $\delta\in(0,\tfrac12]$ and a frame $F\in\{\mathrm L,\mathrm R\}$. Points and vectors of $\mathbb R^3$ are split as $x=(x_0,\bar x)$ with height $x_0\in\mathbb R$ and torus part $\bar x=(x_1,x_2)\in\mathbb R^2$. Let $a(u)=e^{-1/(2/3-u)}$ for $u<\tfrac23$ and $a(u)=0$ otherwise, $A(t)=\int_0^t a(y)\,dy$, and $\chi(t)=\psi\big(6(t-\tfrac5{12})\big)$, where $\psi$ is the standard smooth transition function ($\psi=0$ on $(-\infty,0]$, $\psi=1$ on $[1,\infty)$). The two cometrics are the symmetric $2\times2$ matrices
--   $$P^{\mathrm L}(t)=\begin{pmatrix} d_1(t)+d_2(t)\sigma(t)^2 & d_2(t)\sigma(t)\\ d_2(t)\sigma(t) & d_2(t)\end{pmatrix},\qquad P^{\mathrm R}(t)=K\,P^{\mathrm L}(1-t)\,K^{\mathsf T},$$
--   where $d_1(t)=1+\delta A(t)$, $d_2(t)=1+\delta A(1-t)$, $\sigma(t)=\delta^2\chi(t)$ and $K=\begin{pmatrix}0&1\\1&-\delta^2\end{pmatrix}$. Write $P=P^F$, $Q(t)=P(t)^{-1}$, and $Q',Q''$ for the derivatives of $t\mapsto Q(t)$. The framed neck metric $g=g^F_\delta$ is a smooth Riemannian metric on $\mathbb R^3$ (for $F=\mathrm L$ the normalized neck metric, for $F=\mathrm R$ its pullback under the affine map $y\mapsto(1-y_0,\ \delta^2y_1+y_2,\ y_1)$) which on the slab $-\tfrac14<x_0<\tfrac54$ has the block form
--   $$g_x(u,w)=u_0w_0+\bar u^{\mathsf T}Q(x_0)\,\bar w .$$
--
--   A curve $\gamma:\mathbb R\to\mathbb R^3$ is a geodesic of $g$ on an open set $U$ if it is $C^\infty$ on $U$ and satisfies the geodesic equation of $g$ there ($\mathbb R^3$ carries its identity chart). For a height $t$, vectors $X,Y\in\mathbb R^3$ and $P,Q',Q''$ evaluated at $t$, put
--   $$\Gamma_t(X,Y)=\Big(-\tfrac12\bar X^{\mathsf T}Q'\bar Y,\ \tfrac12\big(X_0PQ'\bar Y+Y_0PQ'\bar X\big)\Big),\qquad \Gamma'_t(X,Y)=\Big(-\tfrac12\bar X^{\mathsf T}Q''\bar Y,\ \tfrac12\big(X_0S\bar Y+Y_0S\bar X\big)\Big),$$
--   with $S=PQ''-PQ'PQ'$, and $\mathcal R_t(X,Y)Z=X_0\Gamma'_t(Y,Z)-Y_0\Gamma'_t(X,Z)+\Gamma_t(X,\Gamma_t(Y,Z))-\Gamma_t(Y,\Gamma_t(X,Z))$; on the slab these are the Christoffel term and the Riemann curvature term of $g$. With $\langle X,Y\rangle_t=X_0Y_0+\bar X^{\mathsf T}Q(t)\bar Y$, the normal index density of a field $W$ along $\gamma$ is
--   $$N_W(s)=\big|\dot W+\Gamma_t(\dot\gamma,W)\big|_t^2-\big\langle W,\mathcal R_t(W,\dot\gamma)\dot\gamma\big\rangle_t-\big\langle\dot W+\Gamma_t(\dot\gamma,W),\dot\gamma\big\rangle_t^2,\qquad t=\gamma_0(s),$$
--   that is, $g(\nabla W,\nabla W)-g(R(W,\dot\gamma)\dot\gamma,W)-g(\nabla W,\dot\gamma)^2$ written in block coordinates. For a field $W$ along $\gamma$ write $t=\gamma_0(s)$, $T=\dot\gamma(s)$, $V=W(s)$ and define the boundary term
--   $$\beta_W(s)=-\tfrac12\,T_0\,\bar V^{\mathsf T}Q'(t)\,\bar V+V_0\,\bar T^{\mathsf T}Q'(t)\,\bar V .$$
--
--   **Statement.** Let $U\subseteq\mathbb R$ be open, $\gamma$ a geodesic of $g=g^F_\delta$ on $U$, and $W:\mathbb R\to\mathbb R^3$ a map that is $C^\infty$ on $U$ with $W_0(s)=0$ for all $s\in U$. Let $a\le b$ with $[a,b]\subseteq U$, and assume $\gamma_0(s)\in[0,1]$ and $g_{\gamma(s)}(\dot\gamma(s),\dot\gamma(s))=1$ for all $s\in[a,b]$, and $\beta_W(b)\le\beta_W(a)$. Then
--   $$\int_a^b N_W(s)\,ds\;\ge\;0 .$$
--
--   Together with the gauge invariance of the normal density, this is the engine behind the index estimates for passages through the neck on which the vertical speed does not vanish: there the vertical component of a test field can be removed by adding a multiple of the velocity, and the endpoint condition is checked from the behaviour of $Q'$ at heights $0$ and $1$.
--
--   **Formalization Note** $N_W$ is `normalDensity` applied to $P$, $Q$, $Q'$, $Q''$ at $\gamma_0(s)$ (`coordinateCometric`, `metricInverse` and its derivatives) and to `splitVector` of $\dot\gamma(s)$, $W(s)$, $\dot W(s)$; $\Gamma_t$, $\Gamma'_t$ and $\mathcal R_t$ are `gamma`, `gammaPrime` and `curvatureJet`, and $\beta_W$ is `boundaryTerm`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean#L745-L831

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

theorem OAI.ThreeManifold.CompactMetric.framed_zeroheight_normal_nonnegative (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ W : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hW : ContDiffOn ℝ ∞ W U) (hW0 : ∀ s ∈ U, W s 0 = 0)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (htr : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hunit : ∀ s ∈ Icc a b, (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1)
    (hboundary : boundaryTerm (deriv (metricInverse right δ) (γ b 0))
      (splitVector (deriv γ b)) (splitVector (W b)) ≤
      boundaryTerm (deriv (metricInverse right δ) (γ a 0)) (splitVector (deriv γ a)) (splitVector (W a))) :
    0 ≤ ∫ s in a..b, normalDensity (coordinateCometric right δ (γ s 0))
      (metricInverse right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
      (deriv (deriv (metricInverse right δ)) (γ s 0))
      (splitVector (deriv γ s)) (splitVector (W s)) (splitVector (deriv W s)) := by sorry

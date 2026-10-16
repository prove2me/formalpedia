-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_finite_neck_index
-- name    : OAI.ThreeManifold.CompactMetric.finite_neck_index
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:05:55.634206+00:00
-- url     : https://prove2.me/theorems/48c12a02-c67b-4188-a2ca-1a2305c486cb
-- title:
--   Nonnegative index on every finite passage of a geodesic through the neck model
-- statement:
--   This is the complete index estimate for one passage of a geodesic through the neck model, with arbitrary (constant) speed and arbitrary entry and exit behaviour.
--
--   **Setting.** Fix $\delta\in(0,\tfrac12]$ and a frame $F\in\{\mathrm L,\mathrm R\}$. Points and vectors of $\mathbb R^3$ are split as $x=(x_0,\bar x)$ with height $x_0\in\mathbb R$ and torus part $\bar x=(x_1,x_2)\in\mathbb R^2$. Let $a(u)=e^{-1/(2/3-u)}$ for $u<\tfrac23$ and $a(u)=0$ otherwise, $A(t)=\int_0^t a(y)\,dy$, and $\chi(t)=\psi\big(6(t-\tfrac5{12})\big)$, where $\psi$ is the standard smooth transition function ($\psi=0$ on $(-\infty,0]$, $\psi=1$ on $[1,\infty)$). The two cometrics are the symmetric $2\times2$ matrices
--   $$P^{\mathrm L}(t)=\begin{pmatrix} d_1(t)+d_2(t)\sigma(t)^2 & d_2(t)\sigma(t)\\ d_2(t)\sigma(t) & d_2(t)\end{pmatrix},\qquad P^{\mathrm R}(t)=K\,P^{\mathrm L}(1-t)\,K^{\mathsf T},$$
--   where $d_1(t)=1+\delta A(t)$, $d_2(t)=1+\delta A(1-t)$, $\sigma(t)=\delta^2\chi(t)$ and $K=\begin{pmatrix}0&1\\1&-\delta^2\end{pmatrix}$. Write $P=P^F$, $Q(t)=P(t)^{-1}$, and $Q',Q''$ for the derivatives of $t\mapsto Q(t)$. The framed neck metric $g=g^F_\delta$ is a smooth Riemannian metric on $\mathbb R^3$ (for $F=\mathrm L$ the normalized neck metric, for $F=\mathrm R$ its pullback under the affine map $y\mapsto(1-y_0,\ \delta^2y_1+y_2,\ y_1)$) which on the slab $-\tfrac14<x_0<\tfrac54$ has the block form
--   $$g_x(u,w)=u_0w_0+\bar u^{\mathsf T}Q(x_0)\,\bar w .$$ In this statement the metric is $g_\delta=g^{\mathrm L}_\delta$, the normalized neck metric; the right cometric $P^{\mathrm R}$ enters only through the hypotheses. Below, $g$ denotes $g_\delta$.
--
--   Here $\mathbb R^3$ carries its single identity chart, so tangent vectors are elements of $\mathbb R^3$. A curve $\gamma:\mathbb R\to\mathbb R^3$ is a geodesic of $g$ on an open set $U\subseteq\mathbb R$ if it is $C^\infty$ on $U$ and $\ddot\gamma(s)+\Gamma_{\gamma(s)}(\dot\gamma(s),\dot\gamma(s))=0$ for all $s\in U$, where $\Gamma_x(u,w)^i=\sum_{j,k}\Gamma^i_{jk}(x)u^jw^k$ is formed with the Christoffel symbols of $g$. A vector field along $\gamma$ is a map $J:\mathbb R\to\mathbb R^3$, called smooth on $U$ if it is $C^\infty$ there; its covariant derivative is $\nabla_sJ=\dot J+\Gamma_{\gamma}(\dot\gamma,J)$ and its index density is
--   $$\mathcal I(s)=g_{\gamma(s)}\big(\nabla_sJ,\nabla_sJ\big)-g_{\gamma(s)}\big(R(J,\dot\gamma)\dot\gamma,\,J\big),$$
--   where $R$ is the Riemann curvature tensor of $g$ with $R(\partial_i,\partial_j)\partial_k=\nabla_i\nabla_j\partial_k-\nabla_j\nabla_i\partial_k$ (so the Jacobi equation reads $\nabla_s^2J+R(J,\dot\gamma)\dot\gamma=0$). Thus $\int_a^b\mathcal I\,ds$ is the index form of $J$ on $[a,b]$.
--
--   Let $a_0=a(0)=e^{-3/2}$, $\beta=\tfrac12\big(1+e^{-9/26}\big)$ and, for $C>0$, $m(C)=a_0+\sqrt{2Ca_0}+2\sqrt{2Ca_0/3}$. Call $\delta$ *$C$-small* if
--   $$0<\delta\le1,\qquad \delta\le\frac{1}{2m(C)},\qquad \delta\le\frac{1-\beta}{2m(C)+3C\,a_0}.$$ Say that $(C,\delta)$ satisfies the *passage bounds* if, for both frames $F\in\{\mathrm L,\mathrm R\}$ and with $P=P^F$, for all $u\in[0,1]$ and $q\in\mathbb R^2$ (with $|q|$ the Euclidean norm)
--   $$\tfrac19|q|^2\le q^{\mathsf T}P(u)q\le18|q|^2,\qquad \big|P'(u)q\big|^2\le C^2\delta^2|q|^2,$$
--   $$q^{\mathsf T}P''(u)\,q\le0,\qquad \big|P'(u)q\big|^2\le C\delta\,q^{\mathsf T}\big(-P''(u)\big)q,$$
--   where $P',\ P''$ are the derivatives of $u\mapsto P(u)$.
--
--   **Statement.** Let $C\ge18$, let $\delta\in(0,\tfrac12]$ be $C$-small, and assume $(C,\delta)$ satisfies the passage bounds. Let $U\subseteq\mathbb R$ be open, $a<b$ with $[a,b]\subseteq U$, $\gamma$ a geodesic of $g_\delta$ on $U$ and $J$ a vector field along $\gamma$ that is smooth on $U$. Assume $\gamma_0(s)\in[0,1]$ for $s\in[a,b]$, $\gamma_0(s)\in(0,1)$ for $s\in(a,b)$, and, at each endpoint $e\in\{a,b\}$, either $\gamma_0(e)\in\{0,1\}$ or $J$ vanishes identically on a neighbourhood of $e$. Then
--   $$\int_a^b\mathcal I(s)\,ds\;\ge\;0 .$$
--
--   No unit-speed, momentum or monotonicity assumption is made: the geodesic may turn around inside the neck, may enter and leave through either boundary component, and its speed (which is constant) may take any value, including $0$. The theorem is the local input for nonnegativity of the index form on the compact manifold, where each maximal passage of a geodesic through the open neck region is lifted to the neck model.
--
--   **Formalization Note** $g_\delta$ is `normalizedNeck hδ`; the smallness condition is `SmallParameter (3*C) (sourceMixed C) δ` and the passage bounds are `PassageBounds C δ`, quantified over the Boolean frame `right` with $P=$ `coordinateCometric right δ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean#L1471-L1529

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
open scoped ContDiff
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem OAI.ThreeManifold.CompactMetric.finite_neck_index {δ C a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hab : a < b) (hsub : Icc a b ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (hrc : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo a b, γ s 0 ∈ Ioo (0:ℝ) 1)
    (ha : (γ a 0 = 0 ∨ γ a 0 = 1) ∨ J =ᶠ[𝓝 a] 0)
    (hb : (γ b 0 = 0 ∨ γ b 0 = 1) ∨ J =ᶠ[𝓝 b] 0) :
    0 ≤ ∫ s in a..b, indexPairDensity (normalizedNeck hδ) γ J J s := by sorry

-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_truncated_return_index
-- name    : OAI.ThreeManifold.CompactMetric.framed_truncated_return_index
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:54:42.033982+00:00
-- url     : https://prove2.me/theorems/e36d8192-d41e-4530-8679-5d7cb70fd80e
-- title:
--   Nonnegative index along a deep returning geodesic arc in the framed neck
-- statement:
--   This is the index estimate for a unit-speed geodesic that enters the neck at height $0$, climbs above height $\tfrac14$, turns around and comes back down.
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
--   Let $a_0=a(0)=e^{-3/2}$, $\beta=\tfrac12\big(1+e^{-9/26}\big)$ and, for $C>0$, $m(C)=a_0+\sqrt{2Ca_0}+2\sqrt{2Ca_0/3}$. Call $\delta$ *$C$-small* if
--   $$0<\delta\le1,\qquad \delta\le\frac{1}{2m(C)},\qquad \delta\le\frac{1-\beta}{2m(C)+3C\,a_0}.$$
--
--   **Statement.** Let $C\ge18$, let $\delta\in(0,\tfrac12]$ be $C$-small, and assume the cometric $P=P^F$ satisfies, for all $u\in[0,1]$ and $q\in\mathbb R^2$ (with $|q|$ the Euclidean norm)
--   $$\tfrac19|q|^2\le q^{\mathsf T}P(u)q\le18|q|^2,\qquad \big|P'(u)q\big|^2\le C^2\delta^2|q|^2,$$
--   $$q^{\mathsf T}P''(u)\,q\le0,\qquad \big|P'(u)q\big|^2\le C\delta\,q^{\mathsf T}\big(-P''(u)\big)q,$$
--   where $P',\ P''$ are the derivatives of $u\mapsto P(u)$.
--   Let $U\subseteq\mathbb R$ be open, let $0<c<L$ with $[0,L]\subseteq U$, let $\gamma$ be a geodesic of $g=g^F_\delta$ on $U$, let $J$ be a vector field along $\gamma$ that is smooth on $U$, and let $p\in\mathbb R^2$. Assume:
--
--   1. (conserved momentum) $Q(\gamma_0(s))\,\dot{\bar\gamma}(s)=p$ for all $s\in[0,L]$;
--   2. (unit speed) $g_{\gamma(s)}(\dot\gamma(s),\dot\gamma(s))=1$ for all $s\in[0,L]$;
--   3. (passage through the neck) $\gamma_0(0)=0$, $\gamma_0(s)\in[0,1]$ for $s\in[0,L]$ and $\gamma_0(s)\in(0,1)$ for $s\in(0,L)$;
--   4. (deep turn) $\dot\gamma_0(c)=0$ and $\gamma_0(c)>\tfrac14$;
--   5. (end condition) $\gamma_0(L)=0$ or $\gamma_0(L)=1$, or else $J$ vanishes identically on a neighbourhood of $L$.
--
--   Then
--   $$\int_0^L\mathcal I(s)\,ds\;\ge\;0 .$$
--
--   In the no-conjugate-points argument the index form along a geodesic is cut into passages through the neck; this result covers the returning passages whose turning point lies above height $\tfrac14$ (passages that stay below $\tfrac14$ see only nonpositive curvature). The end condition allows the arc to be truncated where the test field has already vanished.
--
--   **Formalization Note** The frame is a Boolean `right` (`true` for $\mathrm R$); $P$ is `coordinateCometric right δ`, $Q$ is `metricInverse right δ` (a matrix inverse), the smallness condition is `SmallParameter (3 * C) (sourceMixed C) δ`, the index density is `indexPairDensity (framedNeck right hδ) γ J J`, the momentum hypothesis is stated with `splitVector (deriv γ s)`, and the end condition uses the neighbourhood filter (`J =ᶠ[𝓝 L] 0`). Smoothness of $J$ along $\gamma$ (`SmoothFieldOn`) amounts here to $J$ being $C^\infty$ on $U$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean#L117-L206

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
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem OAI.ThreeManifold.CompactMetric.framed_truncated_return_index (right : Bool) {δ C L c : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3 * C) (sourceMixed C) δ)
    (hb : ∀ u ∈ Icc (0:ℝ) 1, ∀ q : TVec,
      (sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧ qform (coordinateCometric right δ u) q ≤ 18*sqnorm q) ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
      0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc 0 L ⊆ U) (hc : c ∈ Ioo 0 L)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : SmoothFieldOn γ J U) {p : TVec}
    (hp : ∀ s ∈ Icc 0 L, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p)
    (h0 : γ 0 0 = 0)
    (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hend : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hvc : deriv γ c 0 = 0)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (hstar : 1/4 < γ c 0)
    (henergy : ∀ s ∈ Icc 0 L,
      (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (framedNeck right hδ) γ J J s := by sorry

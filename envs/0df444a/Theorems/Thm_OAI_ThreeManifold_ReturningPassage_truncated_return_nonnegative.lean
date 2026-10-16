-- Prove2me | Theorems.Thm_OAI_ThreeManifold_ReturningPassage_truncated_return_nonnegative
-- name    : OAI.ThreeManifold.ReturningPassage.truncated_return_nonnegative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:53:15.964786+00:00
-- url     : https://prove2.me/theorems/ceee8de6-ed3e-4842-92c5-e8a8b4b8fe8c
-- title:
--   Nonnegative normal index form along a possibly truncated returning neck passage
-- statement:
--   Throughout, $\sigma:\mathbb{R}\to[0,1]$ is the standard smooth transition function ($\sigma=0$ on $(-\infty,0]$, $\sigma=1$ on $[1,\infty)$), $a(u)=e^{-1/(2/3-u)}$ for $u<\tfrac23$ and $a(u)=0$ otherwise, $A(u)=\int_0^u a(y)\,dy$, and $\chi(t)=\sigma(6(t-\tfrac{5}{12}))$. For $\delta\in\mathbb{R}$ put $d_1(t)=1+\delta A(t)$, $d_2(t)=1+\delta A(1-t)$, $\theta(t)=\delta^2\chi(t)$ and
--   $$
--   P_\delta(t)=\begin{pmatrix} d_1(t)+d_2(t)\theta(t)^2 & d_2(t)\theta(t)\\ d_2(t)\theta(t) & d_2(t)\end{pmatrix},\qquad C_\delta=\begin{pmatrix}0&1\\1&-\delta^2\end{pmatrix},\qquad P^{\mathrm{end}}_\delta(\tau)=C_\delta\,P_\delta(1-\tau)\,C_\delta^{\top}.
--   $$
--
--   Fix a flag $\rho\in\{\text{left},\text{right}\}$, let $K=K_\rho$ be the cometric $K_{\text{left}}=P_\delta$, $K_{\text{right}}=P^{\mathrm{end}}_\delta$, and $G=K^{-1}$; $K',K''$ and $G',G''$ denote entrywise derivatives in the variable $u$. For $q\in\mathbb{R}^2$ write $|q|^2=q_0^2+q_1^2$, let $e=(1,0)$, and for a fixed momentum $p\in\mathbb{R}^2$ put $F(u)=p^{\top}K'(u)p$ (the force) and $\Phi(u)=p^{\top}K(u)p$ (the potential).
--
--   **Small parameter.** Let $\beta=\tfrac12(1+e^{-9/26})$, $a_0=e^{-3/2}$ and, for $C\in\mathbb{R}$, $m(C)=a_0+\sqrt{2Ca_0}+2\sqrt{2Ca_0/3}$. The condition $\mathrm{Small}(C,\delta)$ means
--   $$
--   0<\delta\le1,\qquad \delta\le\frac{1}{2m(C)},\qquad \delta\le\frac{1-\beta}{2m(C)+3C\,a_0}.
--   $$
--
--   **Normal density.** For $X=(X_0,X'),Y=(Y_0,Y'),Z\in\mathbb{R}\times\mathbb{R}^2$ and a height $u$, set $\langle X,Y\rangle_u=X_0Y_0+X'^{\top}G(u)Y'$,
--   $\Gamma_u(X,Y)=\big(-\tfrac12X'^{\top}G'(u)Y',\ \tfrac12(X_0KG'(u)Y'+Y_0KG'(u)X')\big)$ with $K=K(u)$,
--   $\Gamma^{(1)}_u(X,Y)=\big(-\tfrac12X'^{\top}G''(u)Y',\ \tfrac12(X_0B\,Y'+Y_0B\,X')\big)$ with $B=KG''-KG'KG'$ evaluated at $u$, and
--   $R_u(X,Y)Z=X_0\Gamma^{(1)}_u(Y,Z)-Y_0\Gamma^{(1)}_u(X,Z)+\Gamma_u(X,\Gamma_u(Y,Z))-\Gamma_u(Y,\Gamma_u(X,Z))$.
--   Given functions $t,v:\mathbb{R}\to\mathbb{R}$ and a field $V:\mathbb{R}\to\mathbb{R}\times\mathbb{R}^2$, let $T(s)=(v(s),K(t(s))p)$, $D(s)=V'(s)+\Gamma_{t(s)}(T(s),V(s))$ and
--   $$
--   \mathcal N(s)=\langle D,D\rangle_{t(s)}-\big\langle V(s),\,R_{t(s)}(V(s),T(s))T(s)\big\rangle_{t(s)}-\langle D,T(s)\rangle_{t(s)}^2 .
--   $$
--
--   **Statement.** Let $C\ge18$ and let $\delta$ satisfy $\mathrm{Small}(C,\delta)$. Assume for all $u\in[0,1]$ and $q\in\mathbb{R}^2$:
--   (i) $\tfrac19|q|^2\le q^{\top}K(u)q\le18|q|^2$; (ii) $|K'(u)e|^2\le C^2\delta^2$; (iii) $q^{\top}(-K''(u))q\ge0$; (iv) $|K'(u)p|^2\le C\delta\,p^{\top}(-K''(u))p$.
--   Let $0<c<b$ and let $t,v$ satisfy on $[0,b]$: $t'=v$ and $v'=-\tfrac12F(t)$ at every point, $t$ and $v$ are $C^\infty$ at every point; $t(0)=0$; $t(s)\in(0,1)$ for $s\in(0,b)$; $v(c)=0$ and $t(c)>\tfrac14$; and the energy identity $\Phi(t(s))+v(s)^2=1$ holds for $s\in[0,b]$. Let $V$ be $C^\infty$ at every point of $[0,b]$, assume that if $b<2c$ then $V$ vanishes on a neighbourhood of $b$, and assume $\mathcal N$ is integrable on $[0,b]$. Then
--   $$
--   \int_0^b \mathcal N(s)\,ds\ \ge\ 0 .
--   $$
--
--   Here $(t,v)$ is the height and vertical velocity of a neck geodesic with torus momentum $p$ that leaves the wall $t=0$ at time $0$ and turns at time $c$; $b$ may be the full return time or an earlier time at which the variation field is cut off.
--
--   **Formalization Note** The flag is a Boolean `right`; $K$ is `coordinateCometric right δ`, $G$ is `metricInverse right δ`, $F$ is `force`, $\Phi$ is `potential`, $\mathrm{Small}(C,\delta)$ is `SmallParameter (3*C) (sourceMixed C) δ`, and $\mathcal N$ is `returnNormalDensity right δ p t v V (deriv V)` (built from `normalDensity`, `gamma` and `curvatureJet`). The derivative $V'$ is Lean's `deriv V`, and integrability is `IntervalIntegrable` for Lebesgue measure on $[0,b]$. The bounds (i)–(iv) are hypotheses here, not consequences of the definition of $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean#L20-L105

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

open OAI OAI.ThreeManifold OAI.ThreeManifold.ReturningPassage
open Set Filter Topology MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Elementwise
open Neck Cometric Turning ReturningCoefficients PassageDynamics SupportExtension

theorem OAI.ThreeManifold.ReturningPassage.truncated_return_nonnegative {right : Bool} {δ C b c : ℝ} {p : TVec}
    {t v : ℝ → ℝ} {V : ℝ → Vec} (hC : 18 ≤ C)
    (hδ : SmallParameter (3*C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q, sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18*sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C^2*δ^2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C*δ*qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hc : c ∈ Ioo 0 b) (ht : ∀ s ∈ Icc 0 b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 b, HasDerivAt v (-force right δ p (t s)/2) s)
    (hta : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ t s)
    (hva : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ v s)
    (h0 : t 0 = 0) (hr : ∀ s ∈ Ioo 0 b, t s ∈ Ioo (0:ℝ) 1)
    (hvc : v c = 0) (hstar : 1/4 < t c)
    (henergy : ∀ s ∈ Icc 0 b, potential right δ p (t s) + v s^2 = 1)
    (hV : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ V s)
    (hcut : b < 2*c → V =ᶠ[𝓝 b] 0)
    (hfi : IntervalIntegrable (returnNormalDensity right δ p t v V (deriv V)) volume 0 b) :
    0 ≤ ∫ s in (0:ℝ)..b, returnNormalDensity right δ p t v V (deriv V) s := by sorry

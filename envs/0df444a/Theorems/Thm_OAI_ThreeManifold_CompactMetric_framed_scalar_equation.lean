-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_framed_scalar_equation
-- name    : OAI.ThreeManifold.CompactMetric.framed_scalar_equation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:51:31.367678+00:00
-- url     : https://prove2.me/theorems/56ea382b-66f3-4846-9487-689c2a18b961
-- title:
--   Height equation $\gamma_0''=-\tfrac12\,p^{\top}K'(\gamma_0)\,p$ for geodesics of the framed neck metric
-- statement:
--   Throughout, $\sigma:\mathbb{R}\to[0,1]$ is the standard smooth transition function ($\sigma=0$ on $(-\infty,0]$, $\sigma=1$ on $[1,\infty)$), $a(u)=e^{-1/(2/3-u)}$ for $u<\tfrac23$ and $a(u)=0$ otherwise, $A(u)=\int_0^u a(y)\,dy$, and $\chi(t)=\sigma(6(t-\tfrac{5}{12}))$. For $\delta\in\mathbb{R}$ put $d_1(t)=1+\delta A(t)$, $d_2(t)=1+\delta A(1-t)$, $\theta(t)=\delta^2\chi(t)$ and
--   $$
--   P_\delta(t)=\begin{pmatrix} d_1(t)+d_2(t)\theta(t)^2 & d_2(t)\theta(t)\\ d_2(t)\theta(t) & d_2(t)\end{pmatrix},\qquad C_\delta=\begin{pmatrix}0&1\\1&-\delta^2\end{pmatrix},\qquad P^{\mathrm{end}}_\delta(\tau)=C_\delta\,P_\delta(1-\tau)\,C_\delta^{\top}.
--   $$
--
--   The normalized neck metric $g^{N}$ on $\mathbb{R}^3$ is
--   $$
--   g^{N}_x(u,w)=u_0w_0+\ell_\delta(x_0)^2\,(u_1-\delta^2\chi(x_0)u_2)(w_1-\delta^2\chi(x_0)w_2)+\ell_\delta(1-x_0)^2\,u_2w_2,
--   $$
--   where $\ell_\delta(t)=\exp\!\big(-\int_0^t k_\delta\big)$ with $k_\delta=1-\lambda+\lambda\,\frac{\delta a}{2(1+\delta A)}$ and $\lambda(t)=\sigma(2t+\tfrac32)$. The right-framed metric $g^{R}$ is its pullback $g^{R}_x(u,w)=g^{N}_{\phi(x)}(Lu,Lw)$ under the affine map $\phi(x)=(1-x_0,\ \delta^2x_1+x_2,\ x_1)$ with linear part $L(y)=(-y_0,\ \delta^2y_1+y_2,\ y_1)$.
--
--   For a flag $\rho\in\{\text{left},\text{right}\}$ let $g^\rho$ be the framed neck metric ($g^{\text{left}}=g^N$, $g^{\text{right}}=g^R$) and let $K_\rho$ be the corresponding $2\times2$ cometric, $K_{\text{left}}=P_\delta$, $K_{\text{right}}=P^{\mathrm{end}}_\delta$; write $G_\rho(u)=K_\rho(u)^{-1}$.
--
--   Let $\delta\in(0,\tfrac12]$, let $U\subseteq\mathbb{R}$ be open, and let $\gamma=(\gamma_0,\gamma_1,\gamma_2):\mathbb{R}\to\mathbb{R}^3$ be a geodesic of $g^\rho$ on $U$: $\gamma$ is $C^\infty$ on $U$ and satisfies $\ddot\gamma^i+\Gamma^i_{jk}(\gamma)\dot\gamma^j\dot\gamma^k=0$ at every $s\in U$, where $\Gamma^i_{jk}$ are the Christoffel symbols of $g^\rho$ in the standard coordinates of $\mathbb{R}^3$. Write $y'(r)=(\gamma_1'(r),\gamma_2'(r))$ for the torus part of the velocity. Fix $s\in U$ with $0\le\gamma_0(s)\le1$. Let $p\in\mathbb{R}^2$ be the torus momentum at time $s$, $p=G_\rho(\gamma_0(s))\,y'(s)$, and let $F(u)=p^{\top}K_\rho'(u)\,p$, where $K_\rho'$ is the entrywise derivative of $u\mapsto K_\rho(u)$. Then $r\mapsto\gamma_0'(r)$ is differentiable at $s$ and
--   $$
--   \gamma_0''(s)=-\tfrac12\,F(\gamma_0(s))=-\tfrac12\,p^{\top}K_\rho'(\gamma_0(s))\,p .
--   $$
--
--   Combined with the conservation of the torus momentum, this shows that along a geodesic segment in the slab $0\le x_0\le1$ the height $t=\gamma_0$ solves the autonomous scalar equation $t''=-\tfrac12F(t)$ with a fixed momentum $p$. This is the one-dimensional dynamics that governs neck passages.
--
--   **Formalization Note** The flag is a Boolean `right`; $g^\rho$ is `framedNeck right hδ`, $K_\rho$ is `coordinateCometric right δ`, $G_\rho$ is `metricInverse right δ`, and $F$ is `force right δ p`, defined through `deriv` of the matrix function. The velocity is `deriv γ`, and the torus part is the second component of `splitVector`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L1373-L1398

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
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage

theorem OAI.ThreeManifold.CompactMetric.framed_scalar_equation (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (ht : γ s 0 ∈ Icc (0:ℝ) 1) {p : TVec}
    (hp : metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) :
    HasDerivAt (fun r => deriv γ r 0) (-force right δ p (γ s 0)/2) s := by sorry

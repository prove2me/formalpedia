-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_normalizedRight_bilin
-- name    : OAI.ThreeManifold.CompactMetric.normalizedRight_bilin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:49:49.209304+00:00
-- url     : https://prove2.me/theorems/4f77d936-97d6-48a2-a738-8673d06f2e48
-- title:
--   Block form $1\oplus (P^{\mathrm{end}}_\delta)^{-1}$ of the right-framed neck metric
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
--   Let $\delta\in(0,\tfrac12]$. For every point $x=(x_0,x_1,x_2)\in\mathbb{R}^3$ with $-\tfrac14<x_0<\tfrac54$ and all vectors $u,w\in\mathbb{R}^3$,
--   $$
--   g^{R}_x(u,w)=u_0w_0+\begin{pmatrix}u_1&u_2\end{pmatrix}\,P^{\mathrm{end}}_\delta(x_0)^{-1}\begin{pmatrix}w_1\\w_2\end{pmatrix}.
--   $$
--
--   So on the strip $-\tfrac14<x_0<\tfrac54$ the right-framed neck metric splits orthogonally into the line direction $x_0$ with unit length and a flat two-torus direction whose Gram matrix $P^{\mathrm{end}}_\delta(x_0)^{-1}$ depends only on $x_0$; its inverse $P^{\mathrm{end}}_\delta$ plays the role of the cometric. This is the form in which geodesics and Jacobi fields of the neck are analysed near its right end.
--
--   **Formalization Note** $g^R$ is `normalizedRight hδ` (a `pullback` of `normalizedNeck hδ` along `fromRight δ`), $P^{\mathrm{end}}_\delta(\tau)^{-1}$ is `metricInverse true δ τ` $=$ `(coordinateCometric true δ τ)⁻¹` with `coordinateCometric true δ = PEnd δ`, and the right-hand side is `Neck.metric` applied to the split vectors $(u_0,(u_1,u_2))$ and $(w_0,(w_1,w_2))$. The matrix inverse is Mathlib's `Matrix` inverse, which is a true inverse here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L1233-L1248

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
open RiemannianCoordinates MetricConstruction Cometric Neck LocalNeck ReturningPassage

theorem OAI.ThreeManifold.CompactMetric.normalizedRight_bilin {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (-1/4:ℝ) (5/4)) (u v : E3) :
    (normalizedRight hδ).inner x u v =
      metric (metricInverse true δ (x 0)) (splitVector u) (splitVector v) := by sorry

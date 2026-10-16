-- Prove2me | Theorems.Thm_OAI_ThreeManifold_CompactMetric_realCompactMetric_nonnegative_index
-- name    : OAI.ThreeManifold.CompactMetric.realCompactMetric_nonnegative_index
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:06:30.324434+00:00
-- url     : https://prove2.me/theorems/55f5c53f-4ee4-48f8-8553-b4e2c15f1fa9
-- title:
--   The index form of the compact metric $g_\delta$ is nonnegative along every geodesic segment
-- statement:
--   This is the global index estimate for the explicit metric on the closed three-manifold of the construction.
--
--   **Setting.** Let $\Sigma=\mathbb H/\Gamma$ be the cusped hyperbolic surface of the construction ($\Gamma\le SL(2,\mathbb Z)$ an explicit finite-index subgroup acting on the upper half-plane $\mathbb H$), with its height function $h$, let $\Sigma_8=\{h<\log 8\}$ be its open core and $S^1=\mathbb R/6\mathbb Z$. The closed three-manifold $M$ is obtained from two copies of $\Sigma_8\times S^1$ by gluing their collars: a point of the first copy whose surface coordinate lies in the cusp region $\{\operatorname{Im}z>2\}$, with cusp coordinates $y=\operatorname{Im}z\in(2,8)$, $\theta=\operatorname{Re}z \bmod 6$ and circle coordinate $\varphi$, is identified with the point $(16/y,\ \varphi,\ \theta-\varphi)$ of the second copy. $M$ carries a smooth atlas modelled on $\mathbb R^3$. For $\delta\in(0,\tfrac12]$, $g_\delta$ denotes the smooth Riemannian metric on $M$ built in this formalization: it is nonpositively curved outside the open neck region $N\subset M$ (the image of the collar of the first copy), while across $N$ it is modelled on the normalized neck metric with parameter $\delta$.
--
--   For a curve $\gamma:\mathbb R\to M$ and a vector field $J$ along it ($J(s)\in T_{\gamma(s)}M$), the covariant derivative $\nabla_sJ$ and the curvature term $R(J,\dot\gamma)\dot\gamma$ are computed in charts from the Christoffel symbols of $g_\delta$, and the index density is $\mathcal I(s)=g_\delta(\nabla_sJ,\nabla_sJ)-g_\delta(R(J,\dot\gamma)\dot\gamma,J)$. A geodesic on an open set $U\subseteq\mathbb R$ is a curve that is smooth on $U$ and satisfies the geodesic equation in every chart, and $J$ is smooth along $\gamma$ on $U$ if its coordinate expressions are $C^\infty$ on $U$.
--
--   Let $a(u)=e^{-1/(2/3-u)}$ for $u<\tfrac23$ and $a(u)=0$ otherwise, $A(t)=\int_0^t a(y)\,dy$, and $\chi(t)=\psi\big(6(t-\tfrac5{12})\big)$, where $\psi$ is the standard smooth transition function ($\psi=0$ on $(-\infty,0]$, $\psi=1$ on $[1,\infty)$). The two cometrics are the symmetric $2\times2$ matrices
--   $$P^{\mathrm L}(t)=\begin{pmatrix} d_1(t)+d_2(t)\sigma(t)^2 & d_2(t)\sigma(t)\\ d_2(t)\sigma(t) & d_2(t)\end{pmatrix},\qquad P^{\mathrm R}(t)=K\,P^{\mathrm L}(1-t)\,K^{\mathsf T},$$
--   where $d_1(t)=1+\delta A(t)$, $d_2(t)=1+\delta A(1-t)$, $\sigma(t)=\delta^2\chi(t)$ and $K=\begin{pmatrix}0&1\\1&-\delta^2\end{pmatrix}$.
--
--   Let $a_0=a(0)=e^{-3/2}$, $\beta=\tfrac12\big(1+e^{-9/26}\big)$ and, for $C>0$, $m(C)=a_0+\sqrt{2Ca_0}+2\sqrt{2Ca_0/3}$. Call $\delta$ *$C$-small* if
--   $$0<\delta\le1,\qquad \delta\le\frac{1}{2m(C)},\qquad \delta\le\frac{1-\beta}{2m(C)+3C\,a_0}.$$
--
--   The passage bounds for $(C,\delta)$ are the following conditions on the neck cometrics (which describe the neck metric in its two frames): for both frames $F\in\{\mathrm L,\mathrm R\}$ and $P=P^F$, for all $u\in[0,1]$ and $q\in\mathbb R^2$ (with $|q|$ the Euclidean norm)
--   $$\tfrac19|q|^2\le q^{\mathsf T}P(u)q\le18|q|^2,\qquad \big|P'(u)q\big|^2\le C^2\delta^2|q|^2,$$
--   $$q^{\mathsf T}P''(u)\,q\le0,\qquad \big|P'(u)q\big|^2\le C\delta\,q^{\mathsf T}\big(-P''(u)\big)q,$$
--   where $P',\ P''$ are the derivatives of $u\mapsto P(u)$.
--
--   **Statement.** Let $C\ge18$, let $\delta\in(0,\tfrac12]$ be $C$-small, and assume the passage bounds for $(C,\delta)$. Let $U\subseteq\mathbb R$ be open and order-connected (an open interval, possibly unbounded or empty), and let $\gamma:\mathbb R\to M$ be a geodesic of $g_\delta$ on $U$. Then for every vector field $J$ along $\gamma$ that is smooth on $U$, has compact support, and whose closed support $\operatorname{tsupp}J=\overline{\{s:J(s)\neq0\}}$ is contained in $U$,
--   $$\int_{\mathbb R}\Big(g_\delta(\nabla_sJ,\nabla_sJ)-g_\delta\big(R(J,\dot\gamma)\dot\gamma,J\big)\Big)\,ds\;\ge\;0 .$$
--
--   Nonnegativity of the index form on compactly supported fields along every geodesic segment is the classical criterion that rules out conjugate points; this theorem is therefore the analytic core of the proof that $g_\delta$ has no conjugate points.
--
--   **Formalization Note** $M$ is `GluedConstruction.Manifold`, $g_\delta$ is `realCompactMetric hδ`, $N$ is `openNeck`; the conclusion is `NonnegativeIndexOn (realCompactMetric hδ) γ U`, whose integral is the Lebesgue (Bochner) integral over $\mathbb R$ of `indexPairDensity`. The smallness condition is `SmallParameter (3*C) (sourceMixed C) δ` and the passage bounds are `PassageBounds C δ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean#L1575-L1621

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

theorem OAI.ThreeManifold.CompactMetric.realCompactMetric_nonnegative_index {δ C : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    {γ : ℝ → GluedConstruction.Manifold} (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) :
    NonnegativeIndexOn (realCompactMetric hδ) γ U := by sorry

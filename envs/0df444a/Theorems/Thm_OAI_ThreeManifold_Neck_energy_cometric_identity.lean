-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Neck_energy_cometric_identity
-- name    : OAI.ThreeManifold.Neck.energy_cometric_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:16:08.491623+00:00
-- url     : https://prove2.me/theorems/9e492258-6e9f-44a6-a087-43e3649031f3
-- title:
--   Energy density of $dt^2+Q(t)$ written in terms of the cometric $P=Q^{-1}$
-- statement:
--   For a real $2\times 2$ matrix $A$ and $u,v\in\mathbb{R}^2$ write $\langle u,v\rangle_A = u^{\mathsf T}Av$. Elements of $\mathbb{R}\times\mathbb{R}^2$ are written $U=(U^0,\bar U)$ with $U^0\in\mathbb{R}$ and $\bar U\in\mathbb{R}^2$. For $2\times2$ matrices $Q,A,B$ define the energy density
--   $$
--   e_{Q,A,B}(T,V,\dot V)=(\dot V^0)^2+\langle\dot{\bar V},\dot{\bar V}\rangle_Q+2V^0\langle\dot{\bar V},\bar T\rangle_A+\tfrac12(V^0)^2\langle\bar T,\bar T\rangle_B .
--   $$
--
--   **Theorem.** Let $P,Q,H,K$ be real $2\times2$ matrices with $QP=I$ and $P$, $Q$, $H$ symmetric; $K$ is arbitrary. Then for all $p\in\mathbb{R}^2$, $v\in\mathbb{R}$ and $V,\dot V\in\mathbb{R}\times\mathbb{R}^2$,
--   $$
--   e_{Q,\,-QHQ,\,2QHQHQ-QKQ}\bigl((v,Pp),V,\dot V\bigr)=(\dot V^0)^2+\bigl\langle\dot{\bar V}-V^0Hp,\ \dot{\bar V}-V^0Hp\bigr\rangle_Q-\tfrac12\langle p,p\rangle_K\,(V^0)^2 .
--   $$
--
--   If $Q(t)=P(t)^{-1}$ is a family of metrics on $\mathbb{R}^2$ and $P$ is the cometric with $H=P'$ and $K=P''$, then $-QHQ=Q'$ and $2QHQHQ-QKQ=Q''$. Writing the velocity as $\bar T=Pp$ with momentum $p$, the identity rewrites the energy density as a sum of squares minus a term controlled by the second derivative $K$ of the cometric. So a concave cometric ($K\le 0$) makes the energy density nonnegative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L440-L463

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck

open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.Neck.energy_cometric_identity {P Q H K : TMat} (hQP : Q * P = 1)
    (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hH : Hᵀ = H)
    (p : TVec) (v : ℝ) (V Vdot : Vec) :
    coordinateEnergyDensity Q (-Q * H * Q)
      ((2 : ℝ) • (Q * H * Q * H * Q) - Q * K * Q) (v, P *ᵥ p) V Vdot =
    Vdot.1 ^ 2 + pairing Q (Vdot.2 - V.1 • (H *ᵥ p))
      (Vdot.2 - V.1 • (H *ᵥ p)) - (1 / 2 : ℝ) * pairing K p p * V.1 ^ 2 := by sorry

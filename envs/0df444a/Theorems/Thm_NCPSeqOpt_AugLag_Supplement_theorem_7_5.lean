-- Prove2me | Theorems.Thm_NCPSeqOpt_AugLag_Supplement_theorem_7_5
-- name    : NCPSeqOpt.AugLag.Supplement.theorem_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:58:18.474157+00:00
-- url     : https://prove2.me/theorems/5233797c-1190-4de3-a9a3-1f1590d98a40
-- title:
--   Theorem 7.5, p. 22 — CAKKT-regularity at a feasible point implies Abadie's CQ (T_Ω(x̄) = L_Ω(x̄) and 𝕂_C(x̄, 0) closed)
-- statement:
--   Let $G:\mathbb R^n\to\mathbb E$ be continuously differentiable, $\mathcal K\subseteq\mathbb E$ a nonempty closed convex cone, $\Omega=\{x:G(x)\in\mathcal K\}$, and $\bar x\in\Omega$ a point at which CAKKT-regularity holds. Then Abadie's constraint qualification holds at $\bar x$:
--   $$T_\Omega(\bar x)=L_\Omega(\bar x)\qquad\text{and}\qquad \mathbb K_C(\bar x,0)=\{DG(\bar x)^*\Lambda:\ \langle\Lambda,G(\bar x)\rangle=0,\ \Lambda\in\mathcal K^\circ\}\ \text{is closed},$$
--   where $T_\Omega(\bar x)=\{d:\exists t_k\downarrow0,\ d^k\to d,\ \bar x+t_kd^k\in\Omega\}$ is the tangent cone and $L_\Omega(\bar x)=\{d:DG(\bar x)d\in T_{\mathcal K}(G(\bar x))\}$ the linearized tangent cone.
--
--   Together with Theorem 7.2, this places CAKKT-regularity, the weakest strict constraint qualification for CAKKT, between Robinson's CQ and Abadie's CQ.
--
--   **Formalization Note** $T_\Omega$ is the published `StrictCQ.CAKKT.tangentCone`; $T_{\mathcal K}$ is the same definition on $\mathbb E$. Abadie's CQ in this paper has both clauses, and both are in the conclusion.
--
--   Differences from the source:
--   - reading: "CAKKT-regularity implies Abadie's CQ" → at every feasible x̄; reason: the proof starts "Let x̄ be a feasible point", and Abadie's CQ is defined at feasible points (p. 22).
--   - encoding: t_k ↓ 0 in T_Ω and T_𝒦 → t_k > 0 and t_k → 0; reason: same cone, pass to a decreasing subsequence.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), Theorem 7.5, p. 22 (Abadie's CQ, p. 22)

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_NCPSeqOpt_AugLag_Supplement_Setting

namespace NCPSeqOpt.AugLag.Supplement

open MoreauProx.Decomposition NCPSeqOpt.AugLag
open scoped InnerProductSpace
open Filter Topology

theorem theorem_7_5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) → E) (hG : ContDiff ℝ 1 G)
    (K : Set E) (hK : IsClosedConvexCone K)
    (xbar : EuclideanSpace ℝ (Fin n)) (hfeas : G xbar ∈ K)
    (hreg : IsCAKKTRegular G K xbar) :
    IsAbadieCQ G K xbar := by sorry

end NCPSeqOpt.AugLag.Supplement

-- Prove2me | Theorems.Thm_NCPSeqOpt_AugLag_Supplement_lemma_7_4
-- name    : NCPSeqOpt.AugLag.Supplement.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:57:09.333713+00:00
-- url     : https://prove2.me/theorems/925b0e76-b837-4dfd-970e-2428dc5abf65
-- title:
--   Lemma 7.4, p. 22 — the limiting normal cone N_Ω(x̄) is contained in the outer limit of 𝕂_C(x, r) as (x, r) → (x̄, 0)
-- statement:
--   Let $G:\mathbb R^n\to\mathbb E$ be continuously differentiable, $\mathcal K\subseteq\mathbb E$ a nonempty closed convex cone, $\Omega=\{x:G(x)\in\mathcal K\}$ and $\bar x\in\Omega$. Let
--   $$\widehat N_\Omega(\bar z)=\Big\{w\in\mathbb R^n:\ \limsup_{z\to\bar z,\ z\in\Omega}\frac{\langle w,z-\bar z\rangle}{\|z-\bar z\|}\le0\Big\},\qquad N_\Omega(\bar z)=\limsup_{z\to\bar z,\ z\in\Omega}\widehat N_\Omega(z)$$
--   be the regular and the limiting normal cones. Then, with no constraint qualification,
--   $$N_\Omega(\bar x)\subseteq\limsup_{(x,r)\to(\bar x,0)}\mathbb K_C(x,r).$$
--
--   Combined with CAKKT-regularity, this places the limiting normal cone inside $\mathbb K_C(\bar x,0)$, which is the first step of the proof of Theorem 7.5.
--
--   **Formalization Note** $\widehat N_\Omega$ and $N_\Omega$ are the published `StrictCQ.CAKKT.regNormal` and `StrictCQ.CAKKT.limNormal`; the former states "$\limsup\le0$" as: for every $\varepsilon>0$, $\langle w,z-\bar z\rangle\le\varepsilon\|z-\bar z\|$ for $z\in\Omega$ near $\bar z$. The outer limits are sequential.
--
--   Differences from the source:
--   - reading: "We always have" → at every feasible x̄; reason: N_Ω(x̄) is defined on p. 22 only at points of Ω.
--   - encoding: limsup_{z→z̄, z∈Ω} ‖z − z̄‖⁻¹⟨w, z − z̄⟩ ≤ 0 → for every ε > 0, eventually ⟨w, z − z̄⟩ ≤ ε‖z − z̄‖ for z ∈ Ω; reason: equivalent formulations of the same cone.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), Lemma 7.4, p. 22 (normal cones, p. 22)

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_NCPSeqOpt_AugLag_Supplement_Setting

namespace NCPSeqOpt.AugLag.Supplement

open MoreauProx.Decomposition NCPSeqOpt.AugLag
open scoped InnerProductSpace
open Filter Topology

theorem lemma_7_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) → E) (hG : ContDiff ℝ 1 G)
    (K : Set E) (hK : IsClosedConvexCone K)
    (xbar : EuclideanSpace ℝ (Fin n)) (hfeas : G xbar ∈ K) :
    StrictCQ.CAKKT.limNormal (feasSet G K) xbar ⊆
      StrictCQ.AGP.outerLimitWithin (fun p => KC G K p.1 p.2) Set.univ (xbar, 0) := by sorry

end NCPSeqOpt.AugLag.Supplement

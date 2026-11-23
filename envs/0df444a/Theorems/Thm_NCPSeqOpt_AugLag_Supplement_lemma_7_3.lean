-- Prove2me | Theorems.Thm_NCPSeqOpt_AugLag_Supplement_lemma_7_3
-- name    : NCPSeqOpt.AugLag.Supplement.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:55:15.961156+00:00
-- url     : https://prove2.me/theorems/a69faf23-9bec-489c-9584-1a8711fbfd3d
-- title:
--   Lemma 7.3, p. 22 — under CAKKT-regularity at a feasible x̄, 𝕂_C(x̄, 0) is closed and equals L_Ω(x̄)°
-- statement:
--   Let $G:\mathbb R^n\to\mathbb E$ be continuously differentiable, $\mathcal K\subseteq\mathbb E$ a nonempty closed convex cone, and $\bar x$ a feasible point, $G(\bar x)\in\mathcal K$, at which CAKKT-regularity holds. Then:
--
--   1. the set $\mathbb K_C(\bar x,0)$ is closed;
--   2. it coincides with the polar of the linearized tangent cone,
--   $$\mathbb K_C(\bar x,0)=L_\Omega(\bar x)^\circ,\qquad L_\Omega(\bar x)=\{d\in\mathbb R^n:\ DG(\bar x)d\in T_{\mathcal K}(G(\bar x))\}.$$
--
--   In finite dimension $\mathbb K_C(\bar x,0)$ need not be closed; this lemma supplies the closedness clause of Abadie's CQ in Theorem 7.5.
--
--   **Formalization Note** The polar of a subset of $\mathbb R^n$ is the published `polarCone` ($\langle d,w\rangle\le0$). $T_{\mathcal K}$ is the Bouligand tangent cone with $t_k>0$, $t_k\to0$.
--
--   Differences from the source:
--   - encoding: t_k ↓ 0 in T_𝒦 → t_k > 0 and t_k → 0; reason: same cone, pass to a decreasing subsequence.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), Lemma 7.3, p. 22

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_NCPSeqOpt_AugLag_Supplement_Setting

namespace NCPSeqOpt.AugLag.Supplement

open MoreauProx.Decomposition NCPSeqOpt.AugLag
open scoped InnerProductSpace
open Filter Topology

theorem lemma_7_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) → E) (hG : ContDiff ℝ 1 G)
    (K : Set E) (hK : IsClosedConvexCone K)
    (xbar : EuclideanSpace ℝ (Fin n)) (hfeas : G xbar ∈ K)
    (hreg : IsCAKKTRegular G K xbar) :
    IsClosed (KC G K xbar 0) ∧ KC G K xbar 0 = polarCone (linTangentCone G K xbar) := by sorry

end NCPSeqOpt.AugLag.Supplement

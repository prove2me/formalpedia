-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_K_mem_zSpan_T
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.induce_K_mem_zSpan_T
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:56:08.176439+00:00
-- url     : https://prove2.me/theorems/dc4f5b04-3de7-4223-aea3-f43a28b5d108
-- title:
--   Peterfalvi (1.5.a) at $T$: $\mathrm{Ind}_K^T\theta\in\mathbb{Z}[\mathcal{T}]$ for $Q\not\subseteq\ker\theta$
-- statement:
--   Let $G$ be a finite group which is a minimal simple odd-order group, let `hyp` be a Peterfalvi §13 configuration for $G$ with subgroups $T, K, Q$ (here $K = QD$ is `hyp.K`, and $K, Q \le T$ are viewed inside $T$ via `Subgroup.subgroupOf`), and assume $v d \neq 1$ for its parameters. Let $\theta$ be an irreducible character of $K$ (`IsIrreducibleCharacter θ`, a class function on `↥(hyp.K.subgroupOf hyp.T)`) such that $Q$ is not contained in its kernel, $Q \not\subseteq \ker\theta$. Then the induced class function lies in the integral span of the set $\mathcal{T}$ of the type I–IV setup on $T$:
--   $$\mathrm{Ind}_K^T\,\theta \;\in\; \mathbb{Z}\text{-span}\bigl(\mathcal{T}\bigr),$$
--   where $\mathcal{T}$ is `sSet (hyp.toTypesIIIIIIVSetupT hG hvd)` and the span is `S07.zSpan`.
--
--   The proof induces in two stages through $T' = QV$: constituents of the inner induction with $Q \not\subseteq \ker$ induce into $\mathcal{T}$ by the definition of $\mathcal{T}$. This is the $K$-induced membership step used in the analysis at $T$, mirroring the corresponding statement at $S$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_Tau1T.lean#L260-L374

import Definitions.Def_OddOrder_Peterfalvi_S15_NuRowPin
import Definitions.Def_OddOrder_Peterfalvi_S15_CaseACoherence
import Definitions.Def_OddOrder_Peterfalvi_S15_Tau1T

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in

theorem Hypothesis.induce_K_mem_zSpan_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθQ : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ ∈
      OddOrder.Peterfalvi.S07.zSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) := by sorry

end OddOrder.Peterfalvi.S15

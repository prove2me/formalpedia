-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_K_mem_zSpan_sSet_irr_T
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.induce_K_mem_zSpan_sSet_irr_T
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:55:52.675692+00:00
-- url     : https://prove2.me/theorems/bd27df9b-f643-465d-b686-2c84e4948430
-- title:
--   Peterfalvi (1.5.a) at $T$: irreducible $\mathrm{Ind}_K^T\theta$ lies in $\mathbb{Z}[\mathcal{T}\cap\mathrm{Irr}\,T]$
-- statement:
--   Let $G$ be a finite group which is a minimal simple odd-order group, let `hyp` be a Peterfalvi §13 configuration for $G$ with subgroups $T, K, Q$ (with $K, Q \le T$ viewed inside $T$ via `Subgroup.subgroupOf`), let `pins : NuGridSupplyData hyp`, and assume $vd \neq 1$. Let $\theta$ be an irreducible character of $K$ such that $Q \not\subseteq \ker\theta$, and assume additionally that the induced class function $\mathrm{Ind}_K^T\theta$ is itself an irreducible character of $T$. Then
--   $$\mathrm{Ind}_K^T\,\theta \;\in\; \mathbb{Z}\text{-span}\bigl\{\psi \;:\; \psi\in\mathcal{T},\ \psi \text{ an irreducible character of } T\bigr\},$$
--   where $\mathcal{T}$ is `sSet (hyp.toTypesIIIIIIVSetupT hG hvd)` and the span is `S07.zSpan`.
--
--   This refines the previous membership statement (membership in $\mathbb{Z}[\mathcal{T}]$) for irreducible induced characters: any reducible constituent would be a $\nu$-row, which is orthogonal to $\mathrm{Ind}_K^T\theta$ because the latter is irreducible.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_Tau1T.lean#L376-L583

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

theorem Hypothesis.induce_K_mem_zSpan_sSet_irr_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθQ : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)) :
    ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ ∈
      OddOrder.Peterfalvi.S07.zSpan
        {ψ : ClassFunction ↥hyp.T ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) ∧
          OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ} := by sorry

end OddOrder.Peterfalvi.S15

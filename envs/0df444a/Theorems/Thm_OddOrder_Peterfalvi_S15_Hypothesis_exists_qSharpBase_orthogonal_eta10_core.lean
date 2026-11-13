-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_exists_qSharpBase_orthogonal_eta10_core
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.exists_qSharpBase_orthogonal_eta10_core
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:59:48.215204+00:00
-- url     : https://prove2.me/theorems/9b6d69ab-f860-4c88-8023-b3f079ef67ac
-- title:
--   Peterfalvi (13.8): a $Q^\#$ base orthogonal to $\eta_{10}$ (coefficient-zero choice)
-- statement:
--   Let $G$ be a finite minimal simple group of odd order with no maximal subgroup of type V, and `hyp : Hypothesis (G := G)` the Peterfalvi Section 13 hypothesis package with subgroups $Q\le T$ and `pins : NuGridSupplyData hyp`. Assume $vd\neq1$, that $T$ is of type P (`IsTypeP hyp.T`) with data `Tdata` satisfying $U=V$ (`Tdata.U = hyp.V`), $W_1=W_2'$ and $W_2=W_1'$ (`Tdata.W1 = hyp.W2`, `Tdata.W2 = hyp.W1`), let `chief` be a chief-factor datum for the Types I--V setup of $T$, and assume $D=1$. Then there is an irreducible character $\varphi_0$ of $Q$ (as a subgroup of $T$) such that $Q\not\subseteq\ker\varphi_0$ and
--   $$\big\langle\tau_{1T}\big(\mathrm{Ind}_Q^T\varphi_0\big),\ \eta_{10}\big\rangle=0 ,$$
--   where $\tau_{1T}$ is `hyp.tau1T_ofHonest …`.
--
--   This is the coefficient-zero chosen $Q^\#$ base of Peterfalvi (13.8); it replaces the unavailable assumption that $\mathrm{Ind}_Q^T\varphi_0$ is irreducible in case B.
--
--   **Formalization Note.** The statement is for the scoped `FiniteInduce` and classical instances. The non-containment appears as `¬ (Q ⊆ characterKernel φ₀)` with $Q$ viewed in itself.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseBEndgameSupply/Eta10Correction.lean#L27-L153

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open OddOrder.Peterfalvi.S11 in
open scoped Classical in
open scoped FiniteInduce in

theorem Hypothesis.exists_qSharpBase_orthogonal_eta10_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hD : hyp.D = ⊥) :
    ∃ φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
        ↥(hyp.Q.subgroupOf hyp.T),
      ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
          Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)) ∧
      ClassFunction.inner
        (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
            (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ))) hyp.eta10 = 0 := by sorry

end

end OddOrder.Peterfalvi.S15

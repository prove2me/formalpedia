-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_eta10_cCoeff_base_eq_zero
-- name    : OddOrder.Peterfalvi.S15.eta10_cCoeff_base_eq_zero
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:54:35.190396+00:00
-- url     : https://prove2.me/theorems/67005eab-64eb-4faa-ba9c-0f61f2c7f036
-- title:
--   Peterfalvi (13.7): $\eta_{10}$ has vanishing (7.7.a) coefficients at $P$-nonkernel indices
-- statement:
--   Let $G$ be a finite group (`Fintype G`, $|G|$ invertible in $\mathbb C$) with `IsMinimalSimpleOdd G`, let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration, let `core : CharacterDegreeCore hyp`, and let $\varphi_0$ be an irreducible character of $H=PC$ (as a subgroup of $S$) with $P\not\subseteq\ker\varphi_0$. Here `H_sharp_hypothesis76_base hG hyp φ₀` is the (7.6) family $\zeta_0,\dots,\zeta_n$ of characters of $S$ based at $\mathrm{Ind}_H^S\varphi_0$ and `cCoeff` denotes its (7.7.a) coefficients. Then for every index $i\in\{0,\dots,n\}$ with $P\not\subseteq\ker\zeta_i$,
--
--   $$c_i(\eta_{10})=0 .$$
--
--   Thus, over a base in $\mathcal S_1$, the $\eta_{10}$-coefficients are supported on $P$-kernel indices, which are absorbed into the correction $\alpha$ of (13.5.a).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean#L855-L986

import Definitions.Def_OddOrder_Peterfalvi_S15_CaseACoherence
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S15_Tau1T
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

set_option maxHeartbeats 800000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
open scoped FiniteInduce in

theorem eta10_cCoeff_base_eq_zero [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ))) :
    ∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1),
      ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) →
      (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff hyp.eta10 i = 0 := by sorry

end OddOrder.Peterfalvi.S15

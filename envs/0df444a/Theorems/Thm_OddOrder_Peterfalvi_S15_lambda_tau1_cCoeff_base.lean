-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_tau1_cCoeff_base
-- name    : OddOrder.Peterfalvi.S15.lambda_tau1_cCoeff_base
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:56:42.299679+00:00
-- url     : https://prove2.me/theorems/5e3c1cde-e0e3-49d1-ba09-6da0d76c090f
-- title:
--   Peterfalvi (13.5)/(13.6): (7.7.a) coefficients of $\lambda^{\tau_1}$ over a chosen $\mathcal S_1$-base
-- statement:
--   Let $G$ be a finite group (`Fintype G`, $|G|$ invertible in $\mathbb C$) with `IsMinimalSimpleOdd G`, let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration, and let a `LambdaClusterData hyp` (the $\lambda$-cluster, with character $\lambda=$ `lam.lambda`, a class function on $S$) and `core : CharacterDegreeCore hyp` (Core data providing the $\tau_1$-extension `core.tau1S`). Let $\varphi_0$ be an irreducible character of $H=PC$ (as a subgroup of $S$) with $P\not\subseteq\ker\varphi_0$ and $\mathrm{Ind}_H^S\varphi_0\ne\lambda$. Here `H_sharp_hypothesis76_base hG hyp φ₀` is the (7.6) family $\zeta_0,\dots,\zeta_n$ of characters of $S$ based at $\mathrm{Ind}_H^S\varphi_0$ and `cCoeff` denotes its (7.7.a) coefficients. Suppose $i_1$ is an index with $\zeta_{i_1}=\lambda$. Then
--
--   $$c_{i_1}(\lambda^{\tau_1})=1\quad\text{and}\quad c_i(\lambda^{\tau_1})=0\ \text{ for all } i\ne i_1 \text{ with } P\not\subseteq\ker\zeta_i,$$
--
--   where $\lambda^{\tau_1}=$ `core.tau1S lam.lambda`. The coefficients at $P$-kernel indices are left undetermined.
--
--   This computes the non-kernel part of the expansion of $\lambda^{\tau_1}$ used in (13.5)/(13.6).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean#L648-L853

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

theorem lambda_tau1_cCoeff_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda)
    (i₁ : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1))
    (hi₁eq : (H_sharp_hypothesis76_base hG hyp φ₀).zeta i₁ = lam.lambda) :
    (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) i₁ = 1 ∧
      (∀ i : Fin ((H_sharp_hypothesis76_base hG hyp φ₀).n + 1), i ≠ i₁ →
        ¬ ((hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((H_sharp_hypothesis76_base hG hyp φ₀).zeta i)) →
        (H_sharp_hypothesis76_base hG hyp φ₀).cCoeff (core.tau1S lam.lambda) i = 0) := by sorry

end OddOrder.Peterfalvi.S15

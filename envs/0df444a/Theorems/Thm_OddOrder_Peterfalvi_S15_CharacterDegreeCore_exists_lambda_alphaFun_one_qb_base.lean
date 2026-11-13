-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_exists_lambda_alphaFun_one_qb_base
-- name    : OddOrder.Peterfalvi.S15.CharacterDegreeCore.exists_lambda_alphaFun_one_qb_base
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:58:17.163196+00:00
-- url     : https://prove2.me/theorems/dc48a39f-037d-4f52-b736-ad8dc8ec2a2f
-- title:
--   Peterfalvi (13.6): the correction of $\lambda^{\tau_1}$ at $1$ is a multiple of $q$ (chosen base)
-- statement:
--   Let $G$ be a finite group (`Fintype G`, $|G|$ invertible in $\mathbb C$) with `IsMinimalSimpleOdd G`, let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration, and let a `LambdaClusterData hyp` (the $\lambda$-cluster, with character $\lambda=$ `lam.lambda`, a class function on $S$) and `core : CharacterDegreeCore hyp` (Core data providing the $\tau_1$-extension `core.tau1S`). Let $\varphi_0$ be an irreducible character of $H$ (as a subgroup of $S$) such that $P\not\subseteq\ker\varphi_0$ and $\mathrm{Ind}_H^S\varphi_0\ne\lambda$. Write $\alpha=$ `hypothesis76AlphaFun` for the correction function of the (7.6) family based at $\varphi_0$ (with respect to $P\le S$), applied to the class function $\lambda^{\tau_1}=$ `core.tau1S lam.lambda`. Then there is an integer $b$ with
--
--   $$\alpha(\lambda^{\tau_1})(1)=q\,b .$$
--
--   This is the congruence of (13.6) used to bound the correction term of $\lambda^{\tau_1}$ in the Case B degree argument.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseBEndgameSupply/LambdaCorrection.lean#L256-L393

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped Classical in
open scoped FiniteInduce in

theorem CharacterDegreeCore.exists_lambda_alphaFun_one_qb_base [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(hyp.H.subgroupOf hyp.S))
    (hφ₀P : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)))
    (hφ₀ne : ClassFunction.induce (hyp.H.subgroupOf hyp.S)
        (φ₀ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ) ≠ lam.lambda) :
    ∃ b : ℤ, hypothesis76AlphaFun (H_sharp_hypothesis76_base hG hyp φ₀)
      (hyp.P.subgroupOf hyp.S) (core.tau1S lam.lambda) 1
        = (hyp.q : ℂ) * (b : ℂ) := by sorry

end

end OddOrder.Peterfalvi.S15

-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_lambda_tau1_apply_eq_of_not_mem_H_sat_core
-- name    : OddOrder.Peterfalvi.S15.lambda_tau1_apply_eq_of_not_mem_H_sat_core
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:56:34.26666+00:00
-- url     : https://prove2.me/theorems/8f23ab38-7ef5-4d58-9d0b-97b23ea743d2
-- title:
--   Peterfalvi (13.9.a): off $(H^\#)^G$ the value $\lambda^{\tau_1}(x)$ is $\pm$ an $\eta$-column sum
-- statement:
--   Let $G$ be a finite group with `IsMinimalSimpleOdd G` (and $|G|$ invertible in $\mathbb C$), let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration, and let a `LambdaClusterData hyp` (the $\lambda$-cluster, with character $\lambda=$ `lam.lambda`, a class function on $S$) and `core : CharacterDegreeCore hyp` (Core data providing the $\tau_1$-extension `core.tau1S`). Let $x\in G$ lie outside the conjugacy saturation $(H^\#)^G$ of $H^\#=(PC)\setminus\{1\}$. Then there is $\delta\in\{1,-1\}$ with
--
--   $$\lambda^{\tau_1}(x)=\delta\sum_{i<q}\eta_{i1}(x).$$
--
--   This is the first step of (13.9.a), expressing $\lambda^{\tau_1}$ away from $(H^\#)^G$ through the (13.3.c) column formula.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean#L988-L1053

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

open scoped FiniteInduce in

theorem lambda_tau1_apply_eq_of_not_mem_H_sat_core [Finite G]
    [Invertible (Nat.card G : ℂ)]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) {x : G}
    (hx : x ∉ OddOrder.GroupTheory.conjClassSet (sharpSubgroup hyp.H)) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
      core.tau1S lam.lambda x
        = (δ : ℂ) * ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x := by sorry

end OddOrder.Peterfalvi.S15

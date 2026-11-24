-- Prove2me | Theorems.Thm_GlobalTheory_piTensorDistribMulAction_smul_tprod
-- name    : GlobalTheory.piTensorDistribMulAction_smul_tprod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:34.001354+00:00
-- url     : https://prove2.me/theorems/822c2a99-f8f9-475e-a376-cb40eecd0b6c
-- title:
--   Global Theory: pi Tensor Distrib Mul Action smul tprod
-- statement:
--   The Global Theory construction uses the pi Tensor Distrib Mul Action smul tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L803-L806
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L803-L806

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable (G) {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
  [∀ i, DistribMulAction G (M i)] [∀ i, SMulDistribClass G A (M i)]

theorem GlobalTheory.piTensorDistribMulAction_smul_tprod (g : G) (x : ∀ i, M i) :
    letI := piTensorDistribMulAction G A M
    g • PiTensorProduct.tprod A x = PiTensorProduct.tprod A fun i ↦ g • x i := by sorry

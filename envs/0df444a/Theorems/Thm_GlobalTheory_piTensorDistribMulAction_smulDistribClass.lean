-- Prove2me | Theorems.Thm_GlobalTheory_piTensorDistribMulAction_smulDistribClass
-- name    : GlobalTheory.piTensorDistribMulAction_smulDistribClass
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:46.325433+00:00
-- url     : https://prove2.me/theorems/7ca56a64-d4a0-4452-9b87-a46ec27b4556
-- title:
--   Global Theory: pi Tensor Distrib Mul Action smul Distrib Class
-- statement:
--   The Global Theory construction uses the pi Tensor Distrib Mul Action smul Distrib Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L808-L812
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L808-L812

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

theorem GlobalTheory.piTensorDistribMulAction_smulDistribClass :
    letI := piTensorDistribMulAction G A M
    SMulDistribClass G A (⨂[A] i, M i) := by sorry

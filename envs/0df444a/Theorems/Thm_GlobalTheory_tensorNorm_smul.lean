-- Prove2me | Theorems.Thm_GlobalTheory_tensorNorm_smul
-- name    : GlobalTheory.tensorNorm_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:32.997066+00:00
-- url     : https://prove2.me/theorems/a86c81da-ad1a-4664-b48d-76ab9a63fe3e
-- title:
--   Global Theory: tensor Norm smul
-- statement:
--   The Global Theory construction uses the tensor Norm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L841-L845
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L841-L845

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
variable {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] {ι : Type*}
variable [SMulDistribClass G A M]

theorem GlobalTheory.tensorNorm_smul [Fintype G] (κ : ι ≃ G) (a : A) (x : M) :
    tensorNorm A κ (a • x) = (∏ g : G, g • a) • tensorNorm A κ x := by sorry

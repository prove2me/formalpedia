-- Prove2me | Theorems.Thm_GlobalTheory_tensorNorm_smul_group
-- name    : GlobalTheory.tensorNorm_smul_group
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:05.891876+00:00
-- url     : https://prove2.me/theorems/18346a4c-2791-491d-bcf6-a33a7d108b66
-- title:
--   Global Theory: tensor Norm smul group
-- statement:
--   The Global Theory construction uses the tensor Norm smul group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L834-L837
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L834-L837

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
omit [MulSemiringAction G A]

theorem GlobalTheory.tensorNorm_smul_group [Finite G] [Module.Invertible A M] (κ : ι ≃ G) (g : G) (x : M) :
    tensorNorm A κ (g • x) = tensorNorm A κ x := by sorry

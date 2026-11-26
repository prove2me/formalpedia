-- Prove2me | Theorems.Thm_GlobalTheory_tensorMulSemiringAction_smul_tmul
-- name    : GlobalTheory.tensorMulSemiringAction_smul_tmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:31.362311+00:00
-- url     : https://prove2.me/theorems/c3ea0c61-0f6a-5d51-919b-c943d34b1029
-- title:
--   Global Theory: tensor Mul Semiring Action smul tmul
-- statement:
--   The Global Theory construction uses the tensor Mul Semiring Action smul tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L360-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L360-L362

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
variable (G : Type*) [Group G]
variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

theorem GlobalTheory.tensorMulSemiringAction_smul_tmul (g : G) (s : S) (a : A) :
    letI := tensorMulSemiringAction G R S A
    g • (s ⊗ₜ[R] a) = s ⊗ₜ[R] (g • a) := by sorry

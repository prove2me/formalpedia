-- Prove2me | Theorems.Thm_GlobalTheory_tensorNorm_eq_of_equiv
-- name    : GlobalTheory.tensorNorm_eq_of_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:32.52384+00:00
-- url     : https://prove2.me/theorems/a261cbb3-6905-4cd4-b77d-f6a0fb7351be
-- title:
--   Global Theory: tensor Norm eq of equiv
-- statement:
--   The Global Theory construction uses the tensor Norm eq of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L826-L830
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L826-L830

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

theorem GlobalTheory.tensorNorm_eq_of_equiv [Finite G] [Module.Invertible A M] (κ κ' : ι ≃ G) (x : M) :
    tensorNorm A κ x = tensorNorm A κ' x := by sorry

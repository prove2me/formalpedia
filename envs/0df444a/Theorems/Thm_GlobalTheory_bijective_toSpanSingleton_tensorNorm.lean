-- Prove2me | Theorems.Thm_GlobalTheory_bijective_toSpanSingleton_tensorNorm
-- name    : GlobalTheory.bijective_toSpanSingleton_tensorNorm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:01.771824+00:00
-- url     : https://prove2.me/theorems/831b5eef-1ac7-4fc1-a056-0df98570d5cc
-- title:
--   Global Theory: bijective to Span Singleton tensor Norm
-- statement:
--   The Global Theory construction uses the bijective to Span Singleton tensor Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L856-L860
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L856-L860

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
variable {A}

theorem GlobalTheory.bijective_toSpanSingleton_tensorNorm [Finite G] (κ : ι ≃ G) {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) :
    Function.Bijective (LinearMap.toSpanSingleton A _ (tensorNorm A κ e)) := by sorry

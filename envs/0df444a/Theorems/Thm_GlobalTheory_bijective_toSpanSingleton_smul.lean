-- Prove2me | Theorems.Thm_GlobalTheory_bijective_toSpanSingleton_smul
-- name    : GlobalTheory.bijective_toSpanSingleton_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:37.434802+00:00
-- url     : https://prove2.me/theorems/84c0a050-8661-44bd-b9b2-ed8a731878be
-- title:
--   Global Theory: bijective to Span Singleton smul
-- statement:
--   The Global Theory construction uses the bijective to Span Singleton smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L734-L742
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L734-L742

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
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
variable {A M}

theorem GlobalTheory.bijective_toSpanSingleton_smul {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) (g : G) :
    Function.Bijective (LinearMap.toSpanSingleton A M (g • e)) := by sorry

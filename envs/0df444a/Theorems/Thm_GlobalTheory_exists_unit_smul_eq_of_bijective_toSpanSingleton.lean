-- Prove2me | Theorems.Thm_GlobalTheory_exists_unit_smul_eq_of_bijective_toSpanSingleton
-- name    : GlobalTheory.exists_unit_smul_eq_of_bijective_toSpanSingleton
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:45:19.85192+00:00
-- url     : https://prove2.me/theorems/e27d01b1-7729-472c-8673-4f31d733cf69
-- title:
--   Global Theory: exists unit smul eq of bijective to Span Singleton
-- statement:
--   The Global Theory construction uses the exists unit smul eq of bijective to Span Singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L487-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L487-L495

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
variable {A : Type*} [CommRing A]

theorem GlobalTheory.exists_unit_smul_eq_of_bijective_toSpanSingleton {M : Type*} [AddCommGroup M] [Module A M]
    {e e' : M} (he : Function.Bijective (LinearMap.toSpanSingleton A M e))
    (he' : Function.Bijective (LinearMap.toSpanSingleton A M e')) :
    ∃ u : Aˣ, e' = (u : A) • e := by sorry

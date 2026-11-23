-- Prove2me | Theorems.Thm_GlobalTheory_invertible_of_bijective_toSpanSingleton
-- name    : GlobalTheory.invertible_of_bijective_toSpanSingleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:39.561619+00:00
-- url     : https://prove2.me/theorems/116e63f8-a865-403a-b57a-cfb8bb5aed1c
-- title:
--   Global Theory: invertible of bijective to Span Singleton
-- statement:
--   The Global Theory construction uses the invertible of bijective to Span Singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L483-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L483-L485

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

theorem GlobalTheory.invertible_of_bijective_toSpanSingleton {M : Type*} [AddCommGroup M] [Module A M] {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) : Module.Invertible A M := by sorry

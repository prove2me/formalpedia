-- Prove2me | Theorems.Thm_GlobalTheory_exists_bijective_toSpanSingleton_of_finite_maximalSpectrum
-- name    : GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:17.130752+00:00
-- url     : https://prove2.me/theorems/ae298895-11f4-453e-ac08-c4f75316d09d
-- title:
--   Global Theory: exists bijective to Span Singleton of finite maximal Spectrum
-- statement:
--   The Global Theory construction uses the exists bijective to Span Singleton of finite maximal Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L571-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L571-L579

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
variable {M : Type*} [AddCommGroup M] [Module A M]

theorem GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] [Finite (MaximalSpectrum A)] [Module.Invertible A M] :
    ∃ e : M, Function.Bijective (LinearMap.toSpanSingleton A M e) := by sorry

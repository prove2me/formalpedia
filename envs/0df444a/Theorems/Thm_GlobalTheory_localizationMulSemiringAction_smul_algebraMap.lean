-- Prove2me | Theorems.Thm_GlobalTheory_localizationMulSemiringAction_smul_algebraMap
-- name    : GlobalTheory.localizationMulSemiringAction_smul_algebraMap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:59.173861+00:00
-- url     : https://prove2.me/theorems/ee63aa3c-d779-4675-af4c-b818028ba1df
-- title:
--   Global Theory: localization Mul Semiring Action smul algebra Map
-- statement:
--   The Global Theory construction uses the localization Mul Semiring Action smul algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L425-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L425-L430

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
variable {A : Type*} [CommRing A] [MulSemiringAction G A]

theorem GlobalTheory.localizationMulSemiringAction_smul_algebraMap (U : Submonoid A)
    (hU : ∀ (g : G), ∀ u ∈ U, g • u ∈ U) (A' : Type*) [CommRing A'] [Algebra A A']
    [IsLocalization U A'] (g : G) (a : A) :
    letI := localizationMulSemiringAction G U hU A'
    g • algebraMap A A' a = algebraMap A A' (g • a) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_isRegularLocalRing_atPrime_of_ringEquiv_isLocalization
-- name    : GlobalTheory.isRegularLocalRing_atPrime_of_ringEquiv_isLocalization
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:43.734254+00:00
-- url     : https://prove2.me/theorems/de928b30-8c83-4902-a5ca-c55bdb5cffb8
-- title:
--   Global Theory: is Regular Local Ring at Prime of ring Equiv is Localization
-- statement:
--   The Global Theory construction uses the is Regular Local Ring at Prime of ring Equiv is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingAtPrimeLocalizationTensor.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingAtPrimeLocalizationTensor.lean#L7-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingAtPrimeLocalizationTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.isRegularLocalRing_atPrime_of_ringEquiv_isLocalization {B T T' : Type} [CommRing B]
    [IsRegularRing B] [CommRing T] [CommRing T'] [Algebra B T'] (M : Submonoid B)
    [IsLocalization M T'] (e : T ≃+* T') (𝔫 : Ideal T) [𝔫.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime 𝔫) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_length_eq_sum_length_localizedModule
-- name    : GlobalTheory.length_eq_sum_length_localizedModule
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:40.0788+00:00
-- url     : https://prove2.me/theorems/0f5ef8dc-cd36-549b-8c14-c2d884ed078b
-- title:
--   Global Theory: length eq sum length localized Module
-- statement:
--   The Global Theory construction uses the length eq sum length localized Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L196-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L196-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem GlobalTheory.length_eq_sum_length_localizedModule {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0) :
    Module.length S X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) := by sorry

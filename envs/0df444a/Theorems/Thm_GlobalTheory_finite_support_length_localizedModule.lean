-- Prove2me | Theorems.Thm_GlobalTheory_finite_support_length_localizedModule
-- name    : GlobalTheory.finite_support_length_localizedModule
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:05.269795+00:00
-- url     : https://prove2.me/theorems/543b2cae-18ff-4fd6-8a90-95b5837a25da
-- title:
--   Global Theory: finite support length localized Module
-- statement:
--   The Global Theory construction uses the finite support length localized Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L125-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L125-L141

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
variable {S : Type*} [CommRing S]

theorem GlobalTheory.finite_support_length_localizedModule {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) :
    {n : MaximalSpectrum S | Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) ≠ 0}.Finite := by sorry

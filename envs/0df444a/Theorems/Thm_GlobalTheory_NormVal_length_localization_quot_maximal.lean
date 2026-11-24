-- Prove2me | Theorems.Thm_GlobalTheory_NormVal_length_localization_quot_maximal
-- name    : GlobalTheory.NormVal.length_localization_quot_maximal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:35.378173+00:00
-- url     : https://prove2.me/theorems/abe8763f-1a62-450e-b9a3-037196fb433c
-- title:
--   Norm Val: length localization quot maximal
-- statement:
--   The Norm Val construction uses the length localization quot maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L152-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L152-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]

theorem GlobalTheory.NormVal.length_localization_quot_maximal (m n : MaximalSpectrum S) [Decidable (n = m)]
    (B : Type*) [CommRing B] [Algebra S B] [IsLocalization.AtPrime B n.asIdeal] :
    Module.length B (B ⧸ m.asIdeal.map (algebraMap S B)) = if n = m then 1 else 0 := by sorry

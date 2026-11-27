-- Prove2me | Theorems.Thm_GlobalTheory_isDiscreteValuationRing_localization_of_isDedekindDomain
-- name    : GlobalTheory.isDiscreteValuationRing_localization_of_isDedekindDomain
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:01.886099+00:00
-- url     : https://prove2.me/theorems/d19ffa07-4412-5ed9-a1af-ada5da4d8c80
-- title:
--   Global Theory: is Discrete Valuation Ring localization of is Dedekind Domain
-- statement:
--   The Global Theory construction uses the is Discrete Valuation Ring localization of is Dedekind Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L302-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L302-L306

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
open NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
include R

theorem GlobalTheory.isDiscreteValuationRing_localization_of_isDedekindDomain [IsDedekindDomain S]
    (n : MaximalSpectrum S) : IsDiscreteValuationRing (Localization.AtPrime n.asIdeal) := by sorry

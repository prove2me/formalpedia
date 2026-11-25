-- Prove2me | Theorems.Thm_GlobalTheory_addVal_localization_ne_top
-- name    : GlobalTheory.addVal_localization_ne_top
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:19.358255+00:00
-- url     : https://prove2.me/theorems/412c4bd9-4cc9-441d-978d-61a989212307
-- title:
--   Global Theory: add Val localization ne top
-- statement:
--   The Global Theory construction uses the add Val localization ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L286-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L286-L293

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
variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
variable [∀ n, IsDomain (A n)] [∀ n, IsDiscreteValuationRing (A n)]
include R

theorem GlobalTheory.addVal_localization_ne_top {x : S} (hx : x ∈ nonZeroDivisors S) (n : MaximalSpectrum S) :
    addVal (A n) (algebraMap S (A n) x) ≠ ⊤ := by sorry

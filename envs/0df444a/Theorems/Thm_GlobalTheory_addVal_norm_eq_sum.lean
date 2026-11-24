-- Prove2me | Theorems.Thm_GlobalTheory_addVal_norm_eq_sum
-- name    : GlobalTheory.addVal_norm_eq_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:42.716075+00:00
-- url     : https://prove2.me/theorems/213a2c98-646c-4f1a-a7e3-82b236b7370b
-- title:
--   Global Theory: add Val norm eq sum
-- statement:
--   The Global Theory construction uses the add Val norm eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L254-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L254-L282

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

theorem GlobalTheory.addVal_norm_eq_sum (x : S) :
    addVal R (Algebra.norm R x) = ∑ n : MaximalSpectrum S,
      addVal (A n) (algebraMap S (A n) x) * n.asIdeal.inertiaDeg R := by sorry

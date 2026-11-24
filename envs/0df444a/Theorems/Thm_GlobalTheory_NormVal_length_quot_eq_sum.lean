-- Prove2me | Theorems.Thm_GlobalTheory_NormVal_length_quot_eq_sum
-- name    : GlobalTheory.NormVal.length_quot_eq_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:55.635319+00:00
-- url     : https://prove2.me/theorems/e72ab8d9-a927-4adf-b062-a670f176646f
-- title:
--   Norm Val: length quot eq sum
-- statement:
--   The Norm Val construction uses the length quot eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L201-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L201-L210

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
variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]

theorem GlobalTheory.NormVal.length_quot_eq_sum (I : Ideal S) (hI : Module.length R (S ⧸ I) ≠ ⊤) :
    Module.length R (S ⧸ I) = ∑ n : MaximalSpectrum S,
      Module.length (A n) (A n ⧸ I.map (algebraMap S (A n))) * n.asIdeal.inertiaDeg R := by sorry

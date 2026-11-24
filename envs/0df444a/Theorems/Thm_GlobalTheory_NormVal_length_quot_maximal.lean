-- Prove2me | Theorems.Thm_GlobalTheory_NormVal_length_quot_maximal
-- name    : GlobalTheory.NormVal.length_quot_maximal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:47.509078+00:00
-- url     : https://prove2.me/theorems/df04d8be-3349-4a34-a7fd-5764c2cd915f
-- title:
--   Norm Val: length quot maximal
-- statement:
--   The Norm Val construction uses the length quot maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L101-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L101-L108

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

theorem GlobalTheory.NormVal.length_quot_maximal (n : Ideal S) [n.IsMaximal] :
    Module.length R (S ⧸ n) = n.inertiaDeg R := by sorry

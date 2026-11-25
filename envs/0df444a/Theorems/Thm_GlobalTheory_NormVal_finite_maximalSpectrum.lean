-- Prove2me | Theorems.Thm_GlobalTheory_NormVal_finite_maximalSpectrum
-- name    : GlobalTheory.NormVal.finite_maximalSpectrum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:45.078347+00:00
-- url     : https://prove2.me/theorems/442c53d8-9ef7-40d4-8c0a-f1a7b0623f44
-- title:
--   Norm Val: finite maximal Spectrum
-- statement:
--   The Norm Val construction uses the finite maximal Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L143-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L143-L150

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
include R

theorem GlobalTheory.NormVal.finite_maximalSpectrum : Finite (MaximalSpectrum S) := by sorry

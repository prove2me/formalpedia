-- Prove2me | Theorems.Thm_GlobalTheory_bijective_toPiLocalization_of_henselian
-- name    : GlobalTheory.bijective_toPiLocalization_of_henselian
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:31.116479+00:00
-- url     : https://prove2.me/theorems/cfe13bca-3864-4148-9969-1cb0e1ebc010
-- title:
--   Global Theory: bijective to Pi Localization of henselian
-- statement:
--   The Global Theory construction uses the bijective to Pi Localization of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L408-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L408-L428

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct

theorem GlobalTheory.bijective_toPiLocalization_of_henselian (R S : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] :
    Function.Bijective (MaximalSpectrum.toPiLocalization S) := by sorry

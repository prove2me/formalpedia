-- Prove2me | Theorems.Thm_GlobalTheory_henselianLocalRing_localization_of_henselian
-- name    : GlobalTheory.henselianLocalRing_localization_of_henselian
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:03.390714+00:00
-- url     : https://prove2.me/theorems/616c07a8-2d94-4fc9-b21a-42440d6e4059
-- title:
--   Global Theory: henselian Local Ring localization of henselian
-- statement:
--   The Global Theory construction uses the henselian Local Ring localization of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L402-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L402-L406

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

theorem GlobalTheory.henselianLocalRing_localization_of_henselian (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [q.IsMaximal] : HenselianLocalRing (Localization.AtPrime q) := by sorry

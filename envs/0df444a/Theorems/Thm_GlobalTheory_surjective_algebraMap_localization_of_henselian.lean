-- Prove2me | Theorems.Thm_GlobalTheory_surjective_algebraMap_localization_of_henselian
-- name    : GlobalTheory.surjective_algebraMap_localization_of_henselian
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:05.210251+00:00
-- url     : https://prove2.me/theorems/750727ba-9bca-401b-bb11-53a63d9868ac
-- title:
--   Global Theory: surjective algebra Map localization of henselian
-- statement:
--   The Global Theory construction uses the surjective algebra Map localization of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L368-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L368-L394

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

theorem GlobalTheory.surjective_algebraMap_localization_of_henselian (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [hq : q.IsMaximal] :
    Function.Surjective (algebraMap S (Localization.AtPrime q)) := by sorry

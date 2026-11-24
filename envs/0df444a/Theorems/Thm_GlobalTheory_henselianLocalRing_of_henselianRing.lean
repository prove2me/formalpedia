-- Prove2me | Theorems.Thm_GlobalTheory_henselianLocalRing_of_henselianRing
-- name    : GlobalTheory.henselianLocalRing_of_henselianRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:26:44.593801+00:00
-- url     : https://prove2.me/theorems/4abbad73-71cd-4706-97d6-0fb364ad0055
-- title:
--   Global Theory: henselian Local Ring of henselian Ring
-- statement:
--   The Global Theory construction uses the henselian Local Ring of henselian Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L318-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L318-L320

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

theorem GlobalTheory.henselianLocalRing_of_henselianRing (S : Type*) [CommRing S] [IsLocalRing S]
    [HenselianRing S (maximalIdeal S)] : HenselianLocalRing S := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_henselianLocalRing_of_le_radical
-- name    : GlobalTheory.henselianLocalRing_of_le_radical
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:57.053488+00:00
-- url     : https://prove2.me/theorems/5963d6da-c161-4cad-ae99-87bb017c3610
-- title:
--   Global Theory: henselian Local Ring of le radical
-- statement:
--   The Global Theory construction uses the henselian Local Ring of le radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L81-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L81-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

theorem GlobalTheory.henselianLocalRing_of_le_radical [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
    (hI : maximalIdeal B ≤ I.radical) : HenselianLocalRing B := by sorry

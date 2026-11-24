-- Prove2me | Theorems.Thm_GlobalTheory_henselianLocalRing_of_finite
-- name    : GlobalTheory.henselianLocalRing_of_finite
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:16:58.934273+00:00
-- url     : https://prove2.me/theorems/f42228d4-1f80-4f12-9aa9-67eededbc1e4
-- title:
--   Global Theory: henselian Local Ring of finite
-- statement:
--   The Global Theory construction uses the henselian Local Ring of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L322-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L322-L327

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

theorem GlobalTheory.henselianLocalRing_of_finite (R S : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [IsLocalRing S] :
    HenselianLocalRing S := by sorry

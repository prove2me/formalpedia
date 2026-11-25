-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_comp_fst_card_mul_of_fintype
-- name    : GlobalTheory.hasSum_comp_fst_card_mul_of_fintype
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:11.527818+00:00
-- url     : https://prove2.me/theorems/adcf6abe-4609-4a24-9b21-73c0591cb5f3
-- title:
--   Global Theory: has Sum comp fst card mul of fintype
-- statement:
--   The Global Theory construction uses the has Sum comp fst card mul of fintype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsSmallerLevelRelIndexMul.lean#L7-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsSmallerLevelRelIndexMul.lean#L7-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsSmallerLevelRelIndexMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open QuotientGroup

theorem GlobalTheory.hasSum_comp_fst_card_mul_of_fintype {α β : Type} [Fintype β] (f : α → ℂ) (a : ℂ) (hf : HasSum f a) :
    HasSum (fun p : α × β => f p.1) ((Fintype.card β : ℂ) * a) := by sorry

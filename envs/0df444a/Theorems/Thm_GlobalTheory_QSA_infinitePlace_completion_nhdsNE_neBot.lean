-- Prove2me | Theorems.Thm_GlobalTheory_QSA_infinitePlace_completion_nhdsNE_neBot
-- name    : GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:03:20.90514+00:00
-- url     : https://prove2.me/theorems/550ff84c-40e3-4955-b1e9-eac52d51a9fb
-- title:
--   QSA: infinite Place completion nhds NE ne Bot
-- statement:
--   The QSA construction uses the infinite Place completion nhds NE ne Bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InfinitePlaceCompletionNhdsNEZeroNeBot.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InfinitePlaceCompletionNhdsNEZeroNeBot.lean#L8-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfinitePlaceCompletionNhdsNEZeroNeBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA

theorem GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by sorry

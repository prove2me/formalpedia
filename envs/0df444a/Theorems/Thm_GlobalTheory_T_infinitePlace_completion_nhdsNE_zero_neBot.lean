-- Prove2me | Theorems.Thm_GlobalTheory_T_infinitePlace_completion_nhdsNE_zero_neBot
-- name    : GlobalTheory.T.infinitePlace_completion_nhdsNE_zero_neBot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:47:03.76879+00:00
-- url     : https://prove2.me/theorems/a29ff9d5-1065-447b-baa3-ede50324c46d
-- title:
--   T: infinite Place completion nhds NE zero ne Bot
-- statement:
--   The T construction uses the infinite Place completion nhds NE zero ne Bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InfinitePlaceCompletionNhdsNEZeroNeBotStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InfinitePlaceCompletionNhdsNEZeroNeBotStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfinitePlaceCompletionNhdsNEZeroNeBot
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfinitePlaceCompletionNhdsNEZeroNeBotStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.infinitePlace_completion_nhdsNE_zero_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by sorry

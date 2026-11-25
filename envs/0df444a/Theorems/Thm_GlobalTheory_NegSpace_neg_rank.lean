-- Prove2me | Theorems.Thm_GlobalTheory_NegSpace_neg_rank
-- name    : GlobalTheory.NegSpace.neg_rank
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:41.989088+00:00
-- url     : https://prove2.me/theorems/b8327162-c195-4063-81ba-fb0a30d06a26
-- title:
--   Neg Space: neg rank
-- statement:
--   The Neg Space construction uses the neg rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/NegGram.lean#L27-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/NegGram.lean#L27-L27

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_NegGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions NumberField
open GlobalTheory GlobalTheory.NegSpace
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem GlobalTheory.NegSpace.neg_rank (W : HSpace E) : (neg W).rank = W.rank := by sorry

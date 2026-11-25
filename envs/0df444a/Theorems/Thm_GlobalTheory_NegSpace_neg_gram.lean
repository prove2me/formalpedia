-- Prove2me | Theorems.Thm_GlobalTheory_NegSpace_neg_gram
-- name    : GlobalTheory.NegSpace.neg_gram
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:46.413973+00:00
-- url     : https://prove2.me/theorems/f9a002fc-6889-482e-b3dd-f20407126a5a
-- title:
--   Neg Space: neg gram
-- statement:
--   The Neg Space construction uses the neg gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/NegGram.lean#L29-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/NegGram.lean#L29-L29

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

theorem GlobalTheory.NegSpace.neg_gram (W : HSpace E) : (neg W).gram = -W.gram := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_NegSpace_neg_sig
-- name    : GlobalTheory.NegSpace.neg_sig
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:37.872379+00:00
-- url     : https://prove2.me/theorems/dc4be61d-0ce6-406f-8d3a-ce0ac3b71a4f
-- title:
--   Neg Space: neg sig
-- statement:
--   The Neg Space construction uses the neg sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/NegGram.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/NegGram.lean#L31-L31

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

theorem GlobalTheory.NegSpace.neg_sig (W : HSpace E) (τ : E →+* ℂ) : (neg W).sig τ = ((W.sig τ).2, (W.sig τ).1) := by sorry

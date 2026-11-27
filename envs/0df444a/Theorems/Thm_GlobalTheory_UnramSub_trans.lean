-- Prove2me | Theorems.Thm_GlobalTheory_UnramSub_trans
-- name    : GlobalTheory.UnramSub.trans
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:37.012837+00:00
-- url     : https://prove2.me/theorems/601c4fa4-c88d-58b4-99e8-38593f74e856
-- title:
--   Unram Sub: trans
-- statement:
--   The Unram Sub construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean#L18-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.UnramSub
variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}

theorem GlobalTheory.UnramSub.trans {T₁ T₂ : Subring F} (h₁ : UnramSub i T₁) (h₂ : UnramSub T₁.subtype T₂) : UnramSub i T₂ := by sorry

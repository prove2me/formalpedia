-- Prove2me | Theorems.Thm_GlobalTheory_UnramSub_le
-- name    : GlobalTheory.UnramSub.le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:41.982533+00:00
-- url     : https://prove2.me/theorems/601f8de7-7b37-409a-8a06-abd1060dab7f
-- title:
--   Unram Sub: le
-- statement:
--   The Unram Sub construction uses the le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean#L24-L24

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

theorem GlobalTheory.UnramSub.le {T₁ T₂ : Subring F} (h₂ : UnramSub T₁.subtype T₂) : T₁ ≤ T₂ := by sorry

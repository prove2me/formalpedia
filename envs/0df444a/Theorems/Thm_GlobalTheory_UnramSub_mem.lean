-- Prove2me | Theorems.Thm_GlobalTheory_UnramSub_mem
-- name    : GlobalTheory.UnramSub.mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:55.599804+00:00
-- url     : https://prove2.me/theorems/0e661da2-e9ea-4484-b630-e0964d936658
-- title:
--   Unram Sub: mem
-- statement:
--   The Unram Sub construction uses the mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean#L12-L14

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

theorem GlobalTheory.UnramSub.mem {T : Subring F} (h : UnramSub i T) (v : V) : i v ∈ T := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_UnramSub_range
-- name    : GlobalTheory.UnramSub.range
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:31.447905+00:00
-- url     : https://prove2.me/theorems/e0ad7824-f29d-5d0a-ac81-4490875d9697
-- title:
--   Unram Sub: range
-- statement:
--   The Unram Sub construction uses the range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean#L26-L29

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

theorem GlobalTheory.UnramSub.range [IsDomain V] [IsDiscreteValuationRing V] (hi : Function.Injective i) : UnramSub i i.range := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_RepTrace_isUnit_of_ne_zero
-- name    : GlobalTheory.RepTrace.isUnit_of_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:21:40.429019+00:00
-- url     : https://prove2.me/theorems/e817735b-9506-43da-a0a2-d59d7a414752
-- title:
--   Rep Trace: is Unit of ne zero
-- statement:
--   The Rep Trace construction uses the is Unit of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RepTraceEqMulTrace.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RepTraceEqMulTrace.lean#L7-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepTraceEqMulTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open GlobalTheory.RepTrace

theorem GlobalTheory.RepTrace.isUnit_of_ne_zero {E : Type} [Field E] [NumberField E] {P : Type} [CommRing P] [Algebra ℚ P]
    (g : 𝓞 E →+* P) (b : 𝓞 E) (hb : b ≠ 0) : IsUnit (g b) := by sorry

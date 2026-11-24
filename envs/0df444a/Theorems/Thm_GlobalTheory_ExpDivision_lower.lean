-- Prove2me | Theorems.Thm_GlobalTheory_ExpDivision_lower
-- name    : GlobalTheory.ExpDivision.lower
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:07:09.917628+00:00
-- url     : https://prove2.me/theorems/2362de56-549e-4371-a96e-f7861dee817a
-- title:
--   Exp Division: lower
-- statement:
--   The Exp Division construction uses the lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L196-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L196-L229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision

theorem GlobalTheory.ExpDivision.lower (t : ℝ) :
    1 ≤ 2 * (1 + |t|) ^ 2 * (‖quot (2 * Real.pi) t‖ + ‖quot (2 * Real.pi * √2) t‖) := by sorry

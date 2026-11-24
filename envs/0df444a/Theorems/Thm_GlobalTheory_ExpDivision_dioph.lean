-- Prove2me | Theorems.Thm_GlobalTheory_ExpDivision_dioph
-- name    : GlobalTheory.ExpDivision.dioph
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:07:31.185261+00:00
-- url     : https://prove2.me/theorems/58ff74f1-3b89-4a4d-ac6e-eb1e4be0b654
-- title:
--   Exp Division: dioph
-- statement:
--   The Exp Division construction uses the dioph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L155-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L155-L194

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

theorem GlobalTheory.ExpDivision.dioph (t : ℝ) (hp : round t ≠ 0) :
    1 ≤ 6 * (1 + |t|) * (|t - round t| + |√2 * t - round (√2 * t)|) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_middle
-- name    : GlobalTheory.CompanionTheory.InertSpan.blockVector_middle
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:51:45.07535+00:00
-- url     : https://prove2.me/theorems/bab9c0d7-3f67-403d-9d9b-804b7ba81208
-- title:
--   Inert Span: block Vector middle
-- statement:
--   The Inert Span construction uses the block Vector middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L19-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertSpan
variable {L : Type} [Field L] {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertSpan.blockVector_middle (x : L) (w : Fin N → L) (t : L) (j : Fin N) : vec3 x w t (mid j) = w j := by sorry

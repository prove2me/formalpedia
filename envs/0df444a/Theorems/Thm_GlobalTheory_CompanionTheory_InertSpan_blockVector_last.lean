-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_last
-- name    : GlobalTheory.CompanionTheory.InertSpan.blockVector_last
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:51:08.603287+00:00
-- url     : https://prove2.me/theorems/2933c902-a760-412b-a4fb-5622790008e7
-- title:
--   Inert Span: block Vector last
-- statement:
--   The Inert Span construction uses the block Vector last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L22-L23

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

theorem GlobalTheory.CompanionTheory.InertSpan.blockVector_last (x : L) (w : Fin N → L) (t : L) : vec3 x w t (Fin.last (N + 1)) = t := by sorry

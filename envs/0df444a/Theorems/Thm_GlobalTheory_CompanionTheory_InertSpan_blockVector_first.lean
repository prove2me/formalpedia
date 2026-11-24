-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_first
-- name    : GlobalTheory.CompanionTheory.InertSpan.blockVector_first
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:52:32.682706+00:00
-- url     : https://prove2.me/theorems/809e872c-dbc0-4b83-97ab-25aa82c3d13f
-- title:
--   Inert Span: block Vector first
-- statement:
--   The Inert Span construction uses the block Vector first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L17-L17

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

theorem GlobalTheory.CompanionTheory.InertSpan.blockVector_first (x : L) (w : Fin N → L) (t : L) : vec3 x w t 0 = x := by sorry

attribute [defeq] GlobalTheory.CompanionTheory.InertSpan.blockVector_first

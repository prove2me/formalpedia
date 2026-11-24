-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_sub
-- name    : GlobalTheory.CompanionTheory.InertSpan.blockVector_sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:38.72765+00:00
-- url     : https://prove2.me/theorems/04d91e34-3a48-47c1-a4e0-c4f47d12bf60
-- title:
--   Inert Span: block Vector sub
-- statement:
--   The Inert Span construction uses the block Vector sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L37-L39

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

theorem GlobalTheory.CompanionTheory.InertSpan.blockVector_sub (x x' : Fin N → L) (t t' : L) :
    vec3 (0 : L) x t - vec3 0 x' t' = vec3 0 (x - x') (t - t') := by sorry

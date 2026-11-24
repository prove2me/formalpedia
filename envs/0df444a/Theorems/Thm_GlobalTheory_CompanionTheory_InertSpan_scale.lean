-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_scale
-- name    : GlobalTheory.CompanionTheory.InertSpan.scale
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:04:26.31761+00:00
-- url     : https://prove2.me/theorems/15e2342d-07d8-43ad-a5f0-431a2dce6da4
-- title:
--   Inert Span: scale
-- statement:
--   The Inert Span construction uses the scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L107-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L107-L115

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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertSpan.scale (R : Submodule (intL L) (Fin (N + 2) → L)) {w t : L} (hw : w ≠ 0)
    (hv : Valued.v t ≤ Valued.v w) (h : vec3 (0 : L) 0 w ∈ R) : vec3 (0 : L) 0 t ∈ R := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_det_basis
-- name    : GlobalTheory.CompanionTheory.InertSpan.det_basis
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:13.813531+00:00
-- url     : https://prove2.me/theorems/504bfc24-886b-428e-a88a-1cf796aa3f73
-- title:
--   Inert Span: det basis
-- statement:
--   The Inert Span construction uses the det basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L252-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L252-L267

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

theorem GlobalTheory.CompanionTheory.InertSpan.det_basis (q : Fin (N + 2) → L) (B : Matrix (Fin N) (Fin N) L) (s : Fin N → L) (y : L) :
    (mat3 q (fun k => vec3 (0 : L) (B k) (s k)) (vec3 (0 : L) 0 y)).det = q 0 * y * B.det := by sorry

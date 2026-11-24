-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_vecMul_blockMatrix
-- name    : GlobalTheory.CompanionTheory.InertSpan.vecMul_blockMatrix
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:01.408233+00:00
-- url     : https://prove2.me/theorems/998eedde-4f73-4296-bc00-c49e558e5c49
-- title:
--   Inert Span: vec Mul block Matrix
-- statement:
--   The Inert Span construction uses the vec Mul block Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L64-L67

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

theorem GlobalTheory.CompanionTheory.InertSpan.vecMul_blockMatrix (ρ p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    ρ ᵥ* mat3 p M l = ρ 0 • p + ∑ j, ρ (mid j) • M j + ρ (Fin.last (N + 1)) • l := by sorry

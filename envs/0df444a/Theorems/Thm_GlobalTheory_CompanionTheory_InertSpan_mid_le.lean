-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_mid_le
-- name    : GlobalTheory.CompanionTheory.InertSpan.mid_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:03:51.047488+00:00
-- url     : https://prove2.me/theorems/7881ec58-c8f1-4d12-b78c-8ee3c0935b99
-- title:
--   Inert Span: mid le
-- statement:
--   The Inert Span construction uses the mid le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L122-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L122-L153

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

theorem GlobalTheory.CompanionTheory.InertSpan.mid_le {R : Submodule (intL L) (Fin (N + 2) → L)} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b : Fin N → L}
    (hf : IsFrac g₀ U V C) (h1 : ∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0 ∈ R)
    (h2 : ∀ k, vec3 (0 : L) (g₀ k) ((g₀ *ᵥ b) k) ∈ R) :
    (∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R) ∧
      (∀ i, vec3 (0 : L) 0 (((C * V * g₀) *ᵥ b) i) ∈ R) ∧
      ∀ i, vec3 (0 : L) 0 (((g₀ * C * U) *ᵥ b) i) ∈ R := by sorry

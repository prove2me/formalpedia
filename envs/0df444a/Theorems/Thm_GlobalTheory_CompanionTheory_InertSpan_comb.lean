-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_comb
-- name    : GlobalTheory.CompanionTheory.InertSpan.comb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:43.481476+00:00
-- url     : https://prove2.me/theorems/3ab16386-4fb6-4434-8192-cb631c5ed256
-- title:
--   Inert Span: comb
-- statement:
--   The Inert Span construction uses the comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L98-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L98-L105

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

theorem GlobalTheory.CompanionTheory.InertSpan.comb (R : Submodule (intL L) (Fin (N + 2) → L)) {X : Matrix (Fin N) (Fin N) L} (hX : IsInt X)
    (M : Matrix (Fin N) (Fin N) L) (s : Fin N → L) (h : ∀ k, vec3 (0 : L) (M k) (s k) ∈ R) (i : Fin N) :
    vec3 (0 : L) ((X * M) i) ((X *ᵥ s) i) ∈ R := by sorry

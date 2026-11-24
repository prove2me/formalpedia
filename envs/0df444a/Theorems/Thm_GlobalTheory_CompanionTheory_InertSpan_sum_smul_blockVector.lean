-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_sum_smul_blockVector
-- name    : GlobalTheory.CompanionTheory.InertSpan.sum_smul_blockVector
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:02.389542+00:00
-- url     : https://prove2.me/theorems/7cf221c9-1677-487a-bb7f-08f49761aeec
-- title:
--   Inert Span: sum smul block Vector
-- statement:
--   The Inert Span construction uses the sum smul block Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L41-L44

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

theorem GlobalTheory.CompanionTheory.InertSpan.sum_smul_blockVector (ρ : Fin N → L) (M : Matrix (Fin N) (Fin N) L) (s : Fin N → L) :
    ∑ k, ρ k • vec3 (0 : L) (M k) (s k) = vec3 0 (ρ ᵥ* M) (ρ ⬝ᵥ s) := by sorry

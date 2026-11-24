-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_small_out
-- name    : GlobalTheory.CompanionTheory.InertCount.small_out
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:00:52.673664+00:00
-- url     : https://prove2.me/theorems/44e705b1-d0a9-4fb5-9e96-2d92f0229adc
-- title:
--   Inert Count: small out
-- statement:
--   The Inert Count construction uses the small out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L82-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L82-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}

theorem GlobalTheory.CompanionTheory.InertCount.small_out {e f : ℕ} {C D : Matrix (Fin N) (Fin N) L}
    (hinv : ∀ u ∈ radQ σ N, ∀ k ∈ radQ σ N, k ∈ KU σ (N + 2) → Small ϖ e f C D u → Small ϖ e f C D (u * k))
    (v : radQ σ N) :
    Small ϖ e f C D ((QuotientGroup.mk v : RadQuot σ N).out : radQ σ N).1 ↔ Small ϖ e f C D v.1 := by sorry

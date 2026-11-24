-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_col_zero
-- name    : GlobalTheory.CompanionTheory.InertCount.col_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:02:28.111282+00:00
-- url     : https://prove2.me/theorems/7a5aa877-1fe6-4b74-8803-7806d8d65f08
-- title:
--   Inert Count: col zero
-- statement:
--   The Inert Count construction uses the col zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L11-L17

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

theorem GlobalTheory.CompanionTheory.InertCount.col_zero (hH : Heis) (hU : IsUnramInv ϖ σ q) {w : GU σ (N + 2)} (hw : w ∈ radQ σ N)
    (h0 : rowOf w = 0) : colOf w = 0 := by sorry

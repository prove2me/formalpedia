-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_mul_row_zero
-- name    : GlobalTheory.CompanionTheory.InertCount.mul_row_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:42.568596+00:00
-- url     : https://prove2.me/theorems/95240a5a-24eb-457c-bc30-0d0f8aac6652
-- title:
--   Inert Count: mul row zero
-- statement:
--   The Inert Count construction uses the mul row zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L19-L27

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

theorem GlobalTheory.CompanionTheory.InertCount.mul_row_zero (hH : Heis) (hU : IsUnramInv ϖ σ q) {u w : GU σ (N + 2)} (hu : u ∈ radQ σ N)
    (hw : w ∈ radQ σ N) (h0 : rowOf w = 0) :
    rowOf (u * w) = rowOf u ∧ colOf (u * w) = colOf u ∧ cornerOf (u * w) = cornerOf u + cornerOf w := by sorry

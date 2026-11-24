-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_exists_int_lift
-- name    : GlobalTheory.CompanionTheory.InertCount.exists_int_lift
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:03:17.340835+00:00
-- url     : https://prove2.me/theorems/df154c8e-0913-4391-80a2-e888fde88108
-- title:
--   Inert Count: exists int lift
-- statement:
--   The Inert Count construction uses the exists int lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L61-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L61-L80

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

theorem GlobalTheory.CompanionTheory.InertCount.exists_int_lift (hH : Heis) (hU : IsUnramInv ϖ σ q) (ρ : Fin N → L) (hρ : ∀ j, ρ j ∈ intL L) :
    ∃ k ∈ radQ σ N, k ∈ KU σ (N + 2) ∧ rowOf k = ρ := by sorry

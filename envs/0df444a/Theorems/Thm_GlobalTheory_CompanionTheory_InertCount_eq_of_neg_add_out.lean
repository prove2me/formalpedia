-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_eq_of_neg_add_out
-- name    : GlobalTheory.CompanionTheory.InertCount.eq_of_neg_add_out
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:03:16.33583+00:00
-- url     : https://prove2.me/theorems/fe96a25b-e4d8-43a4-8fac-c8e7ca3d5cfb
-- title:
--   Inert Count: eq of neg add out
-- statement:
--   The Inert Count construction uses the eq of neg add out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L119-L123

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

theorem GlobalTheory.CompanionTheory.InertCount.eq_of_neg_add_out {G : Type*} [AddGroup G] {S : AddSubgroup G} (y y' : G ⧸ S)
    (h : -y.out + y'.out ∈ S) : y = y' := by sorry

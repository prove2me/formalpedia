-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_neg_add_out_mem
-- name    : GlobalTheory.CompanionTheory.InertCount.neg_add_out_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:01:41.661832+00:00
-- url     : https://prove2.me/theorems/5dee7c56-92ba-4c89-9b3d-f7fb7c58e5f0
-- title:
--   Inert Count: neg add out mem
-- statement:
--   The Inert Count construction uses the neg add out mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L125-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L125-L126

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

theorem GlobalTheory.CompanionTheory.InertCount.neg_add_out_mem {G : Type*} [AddGroup G] {S : AddSubgroup G} (a : G) :
    -a + (QuotientAddGroup.mk a : G ⧸ S).out ∈ S := by sorry

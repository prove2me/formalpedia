-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_corner_of_small
-- name    : GlobalTheory.CompanionTheory.InertCount.corner_of_small
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:02:11.35382+00:00
-- url     : https://prove2.me/theorems/5329fc48-2633-411e-8316-e767405bd98b
-- title:
--   Inert Count: corner of small
-- statement:
--   The Inert Count construction uses the corner of small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L49-L59

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

theorem GlobalTheory.CompanionTheory.InertCount.corner_of_small (hH : Heis) (hU : IsUnramInv ϖ σ q) {e f : ℕ} {C D : Matrix (Fin N) (Fin N) L}
    {u w : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hw : w ∈ radQ σ N) (h0 : rowOf w = 0)
    (hs : Small ϖ e f C D u) (hs' : Small ϖ e f C D (u * w)) : ϖ ^ f * cornerOf w ∈ intL L := by sorry

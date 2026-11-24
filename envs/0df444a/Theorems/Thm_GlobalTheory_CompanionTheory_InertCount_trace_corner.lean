-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_trace_corner
-- name    : GlobalTheory.CompanionTheory.InertCount.trace_corner
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:01:08.32013+00:00
-- url     : https://prove2.me/theorems/d449912f-9cda-49e8-bd10-e91a8217d435
-- title:
--   Inert Count: trace corner
-- statement:
--   The Inert Count construction uses the trace corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L29-L34

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

theorem GlobalTheory.CompanionTheory.InertCount.trace_corner (hH : Heis) (hU : IsUnramInv ϖ σ q) {w : GU σ (N + 2)} (hw : w ∈ radQ σ N)
    (h0 : rowOf w = 0) : σ (cornerOf w) + cornerOf w = 0 := by sorry

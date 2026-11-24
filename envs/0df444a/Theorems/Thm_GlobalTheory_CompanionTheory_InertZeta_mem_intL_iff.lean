-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_mem_intL_iff
-- name    : GlobalTheory.CompanionTheory.InertZeta.mem_intL_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:49:21.041083+00:00
-- url     : https://prove2.me/theorems/d009f3b4-883e-4137-a36f-4d50d133f0d2
-- title:
--   Inert Zeta: mem int L iff
-- statement:
--   The Inert Zeta construction uses the mem int L iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/AdditiveVectorExists.lean#L12-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/AdditiveVectorExists.lean#L12-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_AdditiveVectorExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.CompanionTheory.InertZeta.mem_intL_iff {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := by sorry

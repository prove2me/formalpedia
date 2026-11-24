-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_v_det_smul
-- name    : GlobalTheory.CompanionTheory.InertCount.v_det_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:01:29.395864+00:00
-- url     : https://prove2.me/theorems/f255b7c8-3d4a-4901-a21d-d7778f0a1b0b
-- title:
--   Inert Count: v det smul
-- statement:
--   The Inert Count construction uses the v det smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L108-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L108-L117

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

theorem GlobalTheory.CompanionTheory.InertCount.v_det_smul {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (e l : ℕ) {C : Matrix (Fin N) (Fin N) L}
    (hdet : Valued.v C.det = WithZero.exp (-(l : ℤ))) :
    Valued.v (ϖ ^ e • C).det = WithZero.exp (-((l + N * e : ℕ) : ℤ)) := by sorry

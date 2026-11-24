-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_vecMul_smul_apply
-- name    : GlobalTheory.CompanionTheory.InertCount.vecMul_smul_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:03:07.13285+00:00
-- url     : https://prove2.me/theorems/2defb2c0-b473-4510-96ea-7501743e9491
-- title:
--   Inert Count: vec Mul smul apply
-- statement:
--   The Inert Count construction uses the vec Mul smul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L97-L100

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

theorem GlobalTheory.CompanionTheory.InertCount.vecMul_smul_apply (c : L) (r : Fin N → L) (C : Matrix (Fin N) (Fin N) L) (j : Fin N) :
    (r ᵥ* (c • C)) j = c * (r ᵥ* C) j := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_isInt_smul
-- name    : GlobalTheory.CompanionTheory.InertCount.isInt_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:01:21.109795+00:00
-- url     : https://prove2.me/theorems/af417cca-fb7e-47e9-ade0-89f337fcab54
-- title:
--   Inert Count: is Int smul
-- statement:
--   The Inert Count construction uses the is Int smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CountOfHeisenbergIndex.lean#L102-L106

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

theorem GlobalTheory.CompanionTheory.InertCount.isInt_smul {ϖ : L} (hϖ : ϖ ∈ intL L) (e : ℕ) {C : Matrix (Fin N) (Fin N) L} (hC : IsInt C) :
    IsInt (ϖ ^ e • C) := by sorry

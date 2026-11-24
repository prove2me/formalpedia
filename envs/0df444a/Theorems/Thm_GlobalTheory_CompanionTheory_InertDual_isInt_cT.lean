-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_isInt_cT
-- name    : GlobalTheory.CompanionTheory.InertDual.isInt_cT
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:02:20.322108+00:00
-- url     : https://prove2.me/theorems/b58f1f83-e006-4864-b6d0-2f0357b05dc9
-- title:
--   Inert Dual: is Int c T
-- statement:
--   The Inert Dual construction uses the is Int c T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean#L41-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DualPairingExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDual
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertDual.isInt_cT {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {M : Matrix (Fin N) (Fin N) L} (hM : IsInt M) :
    IsInt (cT σ M) := by sorry

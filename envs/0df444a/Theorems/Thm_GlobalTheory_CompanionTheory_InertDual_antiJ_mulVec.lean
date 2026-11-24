-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_antiJ_mulVec
-- name    : GlobalTheory.CompanionTheory.InertDual.antiJ_mulVec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:01:22.891924+00:00
-- url     : https://prove2.me/theorems/4ef7b9f5-dd8b-4127-bb08-c1bbf206a7d8
-- title:
--   Inert Dual: anti J mul Vec
-- statement:
--   The Inert Dual construction uses the anti J mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean#L18-L19

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

theorem GlobalTheory.CompanionTheory.InertDual.antiJ_mulVec (b : Fin N → L) (k : Fin N) : (antiJ L N *ᵥ b) k = b k.rev := by sorry

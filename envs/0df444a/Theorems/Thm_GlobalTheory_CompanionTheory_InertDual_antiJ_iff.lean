-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_antiJ_iff
-- name    : GlobalTheory.CompanionTheory.InertDual.antiJ_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:53:51.326177+00:00
-- url     : https://prove2.me/theorems/4bb770b6-806a-4931-b02c-5214e081895f
-- title:
--   Inert Dual: anti J iff
-- statement:
--   The Inert Dual construction uses the anti J iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean#L12-L16

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

theorem GlobalTheory.CompanionTheory.InertDual.antiJ_iff (i j : Fin N) : i.val + j.val + 1 = N ↔ j = i.rev := by sorry

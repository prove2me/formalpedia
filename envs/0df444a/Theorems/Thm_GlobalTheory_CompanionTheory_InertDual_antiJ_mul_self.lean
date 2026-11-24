-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_antiJ_mul_self
-- name    : GlobalTheory.CompanionTheory.InertDual.antiJ_mul_self
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:57.466903+00:00
-- url     : https://prove2.me/theorems/9ebe07fc-4552-4dcf-9170-6b12cf10b6a5
-- title:
--   Inert Dual: anti J mul self
-- statement:
--   The Inert Dual construction uses the anti J mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean#L21-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DualPairingExists
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self

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

theorem GlobalTheory.CompanionTheory.InertDual.antiJ_mul_self : antiJ L N * antiJ L N = 1 := by sorry

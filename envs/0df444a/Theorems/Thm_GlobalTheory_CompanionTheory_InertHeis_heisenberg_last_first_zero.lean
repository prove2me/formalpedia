-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heisenberg_last_first_zero
-- name    : GlobalTheory.CompanionTheory.InertHeis.heisenberg_last_first_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:57.512953+00:00
-- url     : https://prove2.me/theorems/cbf84bf1-65a3-4f16-a27b-5e8e8668b8fd
-- title:
--   Inert Heis: heisenberg last first zero
-- statement:
--   The Inert Heis construction uses the heisenberg last first zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L288-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L288-L290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
variable (r b : Fin N → L) (c : L)

theorem GlobalTheory.CompanionTheory.InertHeis.heisenberg_last_first_zero : heisMat r b c (Fin.last (N + 1)) 0 = 0 := by sorry

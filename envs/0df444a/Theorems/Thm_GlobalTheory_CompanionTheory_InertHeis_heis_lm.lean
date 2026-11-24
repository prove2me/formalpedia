-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_lm
-- name    : GlobalTheory.CompanionTheory.InertHeis.heis_lm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:52.872029+00:00
-- url     : https://prove2.me/theorems/ea57d66d-8a7a-4249-a98e-13d272a64285
-- title:
--   Inert Heis: heis lm
-- statement:
--   The Inert Heis construction uses the heis lm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L292-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L292-L293

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

theorem GlobalTheory.CompanionTheory.InertHeis.heis_lm (j : Fin N) : heisMat r b c (Fin.last (N + 1)) (mid j) = 0 := by sorry

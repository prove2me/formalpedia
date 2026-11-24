-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_ml
-- name    : GlobalTheory.CompanionTheory.InertHeis.heis_ml
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:56.564711+00:00
-- url     : https://prove2.me/theorems/378d77d3-91ef-4a5d-9bb0-72d737933987
-- title:
--   Inert Heis: heis ml
-- statement:
--   The Inert Heis construction uses the heis ml property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L285-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L285-L286

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

theorem GlobalTheory.CompanionTheory.InertHeis.heis_ml (i : Fin N) : heisMat r b c (mid i) (Fin.last (N + 1)) = b i := by sorry

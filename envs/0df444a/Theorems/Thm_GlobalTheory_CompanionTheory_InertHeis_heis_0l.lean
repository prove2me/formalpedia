-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_0l
-- name    : GlobalTheory.CompanionTheory.InertHeis.heis_0l
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:48:25.109391+00:00
-- url     : https://prove2.me/theorems/ba61e2ea-e735-4b43-b4ee-7025c1c41baf
-- title:
--   Inert Heis: heis 0l
-- statement:
--   The Inert Heis construction uses the heis 0l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L274-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L274-L276

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

theorem GlobalTheory.CompanionTheory.InertHeis.heis_0l : heisMat r b c 0 (Fin.last (N + 1)) = c := by sorry

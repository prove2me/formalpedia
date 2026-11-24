-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heisenberg_middle_first_zero
-- name    : GlobalTheory.CompanionTheory.InertHeis.heisenberg_middle_first_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:22.013916+00:00
-- url     : https://prove2.me/theorems/00fcbad8-3d21-4d55-9dd1-eeca4947f0fe
-- title:
--   Inert Heis: heisenberg middle first zero
-- statement:
--   The Inert Heis construction uses the heisenberg middle first zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L278-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L278-L280

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

theorem GlobalTheory.CompanionTheory.InertHeis.heisenberg_middle_first_zero (i : Fin N) : heisMat r b c (mid i) 0 = 0 := by sorry

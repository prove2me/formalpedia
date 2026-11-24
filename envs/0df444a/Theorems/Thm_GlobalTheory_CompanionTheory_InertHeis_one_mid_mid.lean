-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_one_mid_mid
-- name    : GlobalTheory.CompanionTheory.InertHeis.one_mid_mid
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:19.157192+00:00
-- url     : https://prove2.me/theorems/f755e6f4-dba5-4908-ba94-6962bfe7e941
-- title:
--   Inert Heis: one mid mid
-- statement:
--   The Inert Heis construction uses the one mid mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L300-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L300-L302

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

theorem GlobalTheory.CompanionTheory.InertHeis.one_mid_mid (i j : Fin N) :
    (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) (mid j) = (1 : Matrix (Fin N) (Fin N) L) i j := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_hasLen_diagonal
-- name    : GlobalTheory.CompanionTheory.InertZeta.hasLen_diagonal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:23:24.064675+00:00
-- url     : https://prove2.me/theorems/3937bb4e-379c-4696-8d07-b0bb503b8f63
-- title:
--   Inert Zeta: has Len diagonal
-- statement:
--   The Inert Zeta construction uses the has Len diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/FractionExistsOfSmith.lean#L18-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/FractionExistsOfSmith.lean#L18-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_FractionExistsOfSmith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
open GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.CompanionTheory.InertZeta.hasLen_diagonal {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal fun i => ϖ ^ d i) (∑ i, (-d i).toNat) := by sorry

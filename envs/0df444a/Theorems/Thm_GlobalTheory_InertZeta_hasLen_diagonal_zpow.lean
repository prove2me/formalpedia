-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_hasLen_diagonal_zpow
-- name    : GlobalTheory.InertZeta.hasLen_diagonal_zpow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:18:54.418799+00:00
-- url     : https://prove2.me/theorems/41ef8875-7607-4c41-837b-ec44517e3283
-- title:
--   Inert Zeta: has Len diagonal zpow
-- statement:
--   The Inert Zeta construction uses the has Len diagonal zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixLengthExistsOfElementaryDivisors.lean#L23-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixLengthExistsOfElementaryDivisors.lean#L23-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixLengthExistsOfElementaryDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.InertZeta

theorem GlobalTheory.InertZeta.hasLen_diagonal_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal (fun i => ϖ ^ d i)) (∑ i, (-d i).toNat) := by sorry

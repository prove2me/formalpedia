-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_isInt_diagonal
-- name    : GlobalTheory.InertZeta.isInt_diagonal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:12.397162+00:00
-- url     : https://prove2.me/theorems/c9122bf6-5d51-4e2c-9c5a-becd9b65b79d
-- title:
--   Inert Zeta: is Int diagonal
-- statement:
--   The Inert Zeta construction uses the is Int diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixLengthExistsOfElementaryDivisors.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixLengthExistsOfElementaryDivisors.lean#L16-L21

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

theorem GlobalTheory.InertZeta.isInt_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {f : Fin n → L}
    (hf : ∀ i, f i ∈ intL L) : IsInt (Matrix.diagonal f) := by sorry

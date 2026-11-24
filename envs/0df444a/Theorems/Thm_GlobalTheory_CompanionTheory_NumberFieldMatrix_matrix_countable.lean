-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NumberFieldMatrix_matrix_countable
-- name    : GlobalTheory.CompanionTheory.NumberFieldMatrix.matrix_countable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:31:47.311105+00:00
-- url     : https://prove2.me/theorems/92b5d1f7-ccc3-4df6-975d-b97ffbe8eeef
-- title:
--   Number Field Matrix: matrix countable
-- statement:
--   The Number Field Matrix construction uses the matrix countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountableOfNumberField.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountableOfNumberField.lean#L13-L16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountableOfNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NumberFieldMatrix

theorem GlobalTheory.CompanionTheory.NumberFieldMatrix.matrix_countable :
    ∀ (E : Type) [Field E] [NumberField E] (m n : ℕ),
      Countable (Matrix (Fin m) (Fin n) E) := by sorry

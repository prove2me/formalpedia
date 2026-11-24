-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NumberFieldMatrix_countable_matrix
-- name    : GlobalTheory.CompanionTheory.NumberFieldMatrix.countable_matrix
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:01.540228+00:00
-- url     : https://prove2.me/theorems/581b329b-f6d3-4f7c-8302-0ae7af30fbd4
-- title:
--   Number Field Matrix: countable matrix
-- statement:
--   The Number Field Matrix construction uses the countable matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountableOfNumberField.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountableOfNumberField.lean#L8-L11

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

theorem GlobalTheory.CompanionTheory.NumberFieldMatrix.countable_matrix (E : Type) [Field E] [NumberField E] (m n : ℕ) :
    Countable (Matrix (Fin m) (Fin n) E) := by sorry

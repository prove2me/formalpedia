-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NumberFieldMatrix_countable_of_numberField
-- name    : GlobalTheory.CompanionTheory.NumberFieldMatrix.countable_of_numberField
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:05.8976+00:00
-- url     : https://prove2.me/theorems/a99355fc-bd1b-49b0-9d7d-48ef8e9b558e
-- title:
--   Number Field Matrix: countable of number Field
-- statement:
--   The Number Field Matrix construction uses the countable of number Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountableOfNumberField.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountableOfNumberField.lean#L5-L6

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

theorem GlobalTheory.CompanionTheory.NumberFieldMatrix.countable_of_numberField (E : Type) [Field E] [NumberField E] : Countable E := by sorry

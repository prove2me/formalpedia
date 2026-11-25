-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_not_isTrivialOn_stdChar_neg_one
-- name    : GroundTheory.LocalField.Padic.not_isTrivialOn_stdChar_neg_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:48.077858+00:00
-- url     : https://prove2.me/theorems/b2bd3ae3-3c1b-4397-b45b-12943f3bd444
-- title:
--   Padic: not is Trivial On std Char neg one
-- statement:
--   The Padic construction uses the not is Trivial On std Char neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L200-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L200-L205

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
open GroundTheory.LocalField.Padic
variable (p : ℕ) [hp : Fact p.Prime]

theorem GroundTheory.LocalField.Padic.not_isTrivialOn_stdChar_neg_one : ¬ IsTrivialOn (stdChar p) (-1) := by sorry

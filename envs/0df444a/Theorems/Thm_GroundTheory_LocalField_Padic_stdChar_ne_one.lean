-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_stdChar_ne_one
-- name    : GroundTheory.LocalField.Padic.stdChar_ne_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:13.506158+00:00
-- url     : https://prove2.me/theorems/489aa96c-3869-5fe2-8d2a-96c2658c1120
-- title:
--   Padic: std Char ne one
-- statement:
--   The Padic construction uses the std Char ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L210-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L210-L215

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

theorem GroundTheory.LocalField.Padic.stdChar_ne_one : stdChar p ≠ 1 := by sorry

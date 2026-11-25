-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_stdChar_apply
-- name    : GroundTheory.LocalField.Padic.stdChar_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:37.382552+00:00
-- url     : https://prove2.me/theorems/b839e19f-9c5b-467d-ba7d-3d2769c391aa
-- title:
--   Padic: std Char apply
-- statement:
--   The Padic construction uses the std Char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L170-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L170-L172

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

theorem GroundTheory.LocalField.Padic.stdChar_apply (x : ℚ_[p]) (m : ℤ) (k : ℕ) (h : ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1) :
    stdChar p x = Real.fourierChar (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) := by sorry

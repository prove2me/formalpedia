-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_stdChar_intCast_div_pow
-- name    : GroundTheory.LocalField.Padic.stdChar_intCast_div_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:33.151234+00:00
-- url     : https://prove2.me/theorems/1487fb15-1c45-4535-a57a-b8ba7239522f
-- title:
--   Padic: std Char int Cast div pow
-- statement:
--   The Padic construction uses the std Char int Cast div pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L174-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L174-L176

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

theorem GroundTheory.LocalField.Padic.stdChar_intCast_div_pow (m : ℤ) (k : ℕ) :
    stdChar p ((m : ℚ_[p]) / (p : ℚ_[p]) ^ k) = Real.fourierChar (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) := by sorry

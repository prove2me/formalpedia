-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_ord_p
-- name    : GroundTheory.LocalField.Padic.ord_p
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:28.254338+00:00
-- url     : https://prove2.me/theorems/c4a909cf-fdc1-4bcc-8d66-fdf0184f6727
-- title:
--   Padic: ord p
-- statement:
--   The Padic construction uses the ord p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L49-L51

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

theorem GroundTheory.LocalField.Padic.ord_p : ord (p : ℚ_[p]) = 1 := by sorry

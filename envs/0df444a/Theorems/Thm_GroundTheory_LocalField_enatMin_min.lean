-- Prove2me | Theorems.Thm_GroundTheory_LocalField_enatMin_min
-- name    : GroundTheory.LocalField.enatMin_min
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:43.546475+00:00
-- url     : https://prove2.me/theorems/f6bc26d5-538e-47b4-8181-ed7c8fb96ab2
-- title:
--   Local Field: enat Min min
-- statement:
--   The Local Field construction uses the enat Min min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L11-L19

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Definitions.Def_GroundTheory_LocalFields_UpperNumbering
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
open ValuativeRel

theorem GroundTheory.LocalField.enatMin_min (n N : ℕ∞) (a : ℝ) : enatMin (min n N) a = enatMin n (enatMin N a) := by sorry

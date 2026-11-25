-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ratCircleChar_eq_one_iff
-- name    : GroundTheory.LocalField.ratCircleChar_eq_one_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:33.353062+00:00
-- url     : https://prove2.me/theorems/69b511c3-6344-5d82-a338-c9d5c67519c4
-- title:
--   Local Field: rat Circle Char eq one iff
-- statement:
--   The Local Field construction uses the rat Circle Char eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean#L43-L49

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
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
open ValuativeRel Topology Filter
open scoped WithZero Pointwise

theorem GroundTheory.LocalField.ratCircleChar_eq_one_iff {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by sorry

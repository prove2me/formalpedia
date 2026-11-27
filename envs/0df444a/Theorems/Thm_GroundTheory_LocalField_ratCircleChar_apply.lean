-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ratCircleChar_apply
-- name    : GroundTheory.LocalField.ratCircleChar_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:07.925094+00:00
-- url     : https://prove2.me/theorems/f5d77364-940e-590a-b70b-a1a74ec6b440
-- title:
--   Local Field: rat Circle Char apply
-- statement:
--   The Local Field construction uses the rat Circle Char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean#L37-L38

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

theorem GroundTheory.LocalField.ratCircleChar_apply (x : AddCircle (1 : ℚ)) :
    ratCircleChar x = AddCircle.toCircle (ratAddCircleToReal x) := by sorry

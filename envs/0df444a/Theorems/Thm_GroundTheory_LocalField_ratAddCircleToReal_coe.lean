-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ratAddCircleToReal_coe
-- name    : GroundTheory.LocalField.ratAddCircleToReal_coe
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:14.373578+00:00
-- url     : https://prove2.me/theorems/39cd2107-e2c1-5159-870c-3987ff9aac6b
-- title:
--   Local Field: rat Add Circle To Real coe
-- statement:
--   The Local Field construction uses the rat Add Circle To Real coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean#L19-L20

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

theorem GroundTheory.LocalField.ratAddCircleToReal_coe (q : ℚ) :
    ratAddCircleToReal (q : AddCircle (1 : ℚ)) = ((q : ℝ) : AddCircle (1 : ℝ)) := by sorry

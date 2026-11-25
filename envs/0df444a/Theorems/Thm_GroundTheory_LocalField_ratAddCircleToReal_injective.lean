-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ratAddCircleToReal_injective
-- name    : GroundTheory.LocalField.ratAddCircleToReal_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:05:11.598797+00:00
-- url     : https://prove2.me/theorems/75cfe3bf-f337-422d-9a5c-f7bcc7461849
-- title:
--   Local Field: rat Add Circle To Real injective
-- statement:
--   The Local Field construction uses the rat Add Circle To Real injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean#L22-L32

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

theorem GroundTheory.LocalField.ratAddCircleToReal_injective : Function.Injective ratAddCircleToReal := by sorry

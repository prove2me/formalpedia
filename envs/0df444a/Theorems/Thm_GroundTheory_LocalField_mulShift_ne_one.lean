-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mulShift_ne_one
-- name    : GroundTheory.LocalField.mulShift_ne_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:31:53.113591+00:00
-- url     : https://prove2.me/theorems/2617dc00-0414-451a-88b7-1adabe60c5d6
-- title:
--   Local Field: mul Shift ne one
-- statement:
--   The Local Field construction uses the mul Shift ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierChar.lean#L147-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierChar.lean#L147-L148

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
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
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (ψ : AddChar K Circle)
variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
omit hψ [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.mulShift_ne_one {a : K} (ha : a ≠ 0) : ψ.mulShift a ≠ 1 := by sorry

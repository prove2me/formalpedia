-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_schwartzBruhat
-- name    : GroundTheory.LocalField.mem_schwartzBruhat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:11:12.102494+00:00
-- url     : https://prove2.me/theorems/7a0b3c9a-6105-5a5e-9b3f-a6e6c7d50e35
-- title:
--   Local Field: mem schwartz Bruhat
-- statement:
--   The Local Field construction uses the mem schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L24-L25

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
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
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
omit [Field K] [ValuativeRel K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.mem_schwartzBruhat {f : K → ℂ} :
    f ∈ schwartzBruhat K ↔ IsLocallyConstant f ∧ HasCompactSupport f := by sorry

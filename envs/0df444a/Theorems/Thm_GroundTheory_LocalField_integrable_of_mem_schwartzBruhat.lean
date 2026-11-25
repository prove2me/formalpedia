-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integrable_of_mem_schwartzBruhat
-- name    : GroundTheory.LocalField.integrable_of_mem_schwartzBruhat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:17:24.710868+00:00
-- url     : https://prove2.me/theorems/db289dbf-3ae3-5595-9a7b-e095339357bc
-- title:
--   Local Field: integrable of mem schwartz Bruhat
-- statement:
--   The Local Field construction uses the integrable of mem schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L128-L130

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
variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
variable (ψ : AddChar K Circle)
omit [ValuativeRel K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.integrable_of_mem_schwartzBruhat {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    Integrable f μ := by sorry

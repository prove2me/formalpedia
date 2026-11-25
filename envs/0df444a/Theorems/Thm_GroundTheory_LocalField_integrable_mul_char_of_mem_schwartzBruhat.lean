-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integrable_mul_char_of_mem_schwartzBruhat
-- name    : GroundTheory.LocalField.integrable_mul_char_of_mem_schwartzBruhat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:52:59.307697+00:00
-- url     : https://prove2.me/theorems/e3b9262e-e6f5-465c-a3e0-048a11d9fe49
-- title:
--   Local Field: integrable mul char of mem schwartz Bruhat
-- statement:
--   The Local Field construction uses the integrable mul char of mem schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L136-L139

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
variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
omit hψ1

theorem GroundTheory.LocalField.integrable_mul_char_of_mem_schwartzBruhat {f : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (y : K) : Integrable (fun x => f x * (ψ (x * y) : ℂ)) μ := by sorry

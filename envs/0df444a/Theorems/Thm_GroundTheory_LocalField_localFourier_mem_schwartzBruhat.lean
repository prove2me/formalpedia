-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localFourier_mem_schwartzBruhat
-- name    : GroundTheory.LocalField.localFourier_mem_schwartzBruhat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:08:33.458719+00:00
-- url     : https://prove2.me/theorems/aa654e70-a71c-50c3-ad1e-abb56cf8de0b
-- title:
--   Local Field: local Fourier mem schwartz Bruhat
-- statement:
--   The Local Field construction uses the local Fourier mem schwartz Bruhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L175-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L175-L181

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

theorem GroundTheory.LocalField.localFourier_mem_schwartzBruhat {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    localFourier μ ψ f ∈ schwartzBruhat K := by sorry

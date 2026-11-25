-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localFourier_localFourier_selfDual
-- name    : GroundTheory.LocalField.localFourier_localFourier_selfDual
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:58.931845+00:00
-- url     : https://prove2.me/theorems/b73c6036-3572-5c28-9ec8-40b33bd68924
-- title:
--   Local Field: local Fourier local Fourier self Dual
-- statement:
--   The Local Field construction uses the local Fourier local Fourier self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L77-L82

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

theorem GroundTheory.LocalField.localFourier_localFourier_selfDual {f : K → ℂ} (hf : f ∈ schwartzBruhat K) (x : K) :
    localFourier (selfDualMeasure ψ) ψ (localFourier (selfDualMeasure ψ) ψ f) x = f (-x) := by sorry

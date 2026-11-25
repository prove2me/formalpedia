-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localFourier_localFourier
-- name    : GroundTheory.LocalField.localFourier_localFourier
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:36.769226+00:00
-- url     : https://prove2.me/theorems/845ba07e-ab88-57c5-b6c2-6dca01831d2d
-- title:
--   Local Field: local Fourier local Fourier
-- statement:
--   The Local Field construction uses the local Fourier local Fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L183-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L183-L258

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

theorem GroundTheory.LocalField.localFourier_localFourier {f : K → ℂ} (hf : f ∈ schwartzBruhat K) (z : K) :
    localFourier μ ψ (localFourier μ ψ f) z =
      (((residueCard K : ℝ) ^ (-addCharConductor ψ) * μ.real (valBall K 0) ^ 2 : ℝ) : ℂ) * f (-z) := by sorry

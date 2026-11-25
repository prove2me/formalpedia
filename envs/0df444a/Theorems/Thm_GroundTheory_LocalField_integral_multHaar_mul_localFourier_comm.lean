-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integral_multHaar_mul_localFourier_comm
-- name    : GroundTheory.LocalField.integral_multHaar_mul_localFourier_comm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:11:47.743324+00:00
-- url     : https://prove2.me/theorems/dd418c28-3869-56be-a391-29ad03be951e
-- title:
--   Local Field: integral mult Haar mul local Fourier comm
-- statement:
--   The Local Field construction uses the integral mult Haar mul local Fourier comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaTate.lean#L82-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaTate.lean#L82-L102

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
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
  [MeasurableSpace K] [BorelSpace K]
variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
include hψ

theorem GroundTheory.LocalField.integral_multHaar_mul_localFourier_comm {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) (y : K) :
    ∫ u, f u * localFourier μ ψ g ((u : K) * y) * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K =
      ∫ u, g u * localFourier μ ψ f ((u : K) * y) * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K := by sorry

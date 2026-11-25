-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localZeta_mul_localZeta_fourier_eq
-- name    : GroundTheory.LocalField.localZeta_mul_localZeta_fourier_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:07.882989+00:00
-- url     : https://prove2.me/theorems/d036c1e6-389d-5594-9ee2-826cbed71fde
-- title:
--   Local Field: local Zeta mul local Zeta fourier eq
-- statement:
--   The Local Field construction uses the local Zeta mul local Zeta fourier eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaTate.lean#L112-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaTate.lean#L112-L168

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
  (hψ1 : ψ ≠ 1) {χ : Kˣ →* ℂˣ} (hχ : Continuous χ)
include hψ hψ1 hχ

theorem GroundTheory.LocalField.localZeta_mul_localZeta_fourier_eq {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) {s : ℂ} (hs1 : -quasiCharExponent χ < s.re)
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta f χ s * localZeta (localFourier μ ψ g) χ⁻¹ (1 - s) =
      ∫ y, ((χ y : ℂˣ) : ℂ)⁻¹ * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) *
        ∫ x, f x * localFourier μ ψ g ((x : K) * (y : K)) * ((modulus (x : K) : ℝ) : ℂ)
          ∂multHaar K ∂multHaar K := by sorry

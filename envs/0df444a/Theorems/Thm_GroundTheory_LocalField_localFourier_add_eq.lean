-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localFourier_add_eq
-- name    : GroundTheory.LocalField.localFourier_add_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:13.708579+00:00
-- url     : https://prove2.me/theorems/c3482ed7-98ed-5689-9379-a2d2d9306615
-- title:
--   Local Field: local Fourier add eq
-- statement:
--   The Local Field construction uses the local Fourier add eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L162-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L162-L173

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
omit [BorelSpace K] [μ.IsAddHaarMeasure]

theorem GroundTheory.LocalField.localFourier_add_eq {f : K → ℂ} {M : ℤ} (hfM : ∀ x, f x ≠ 0 → x ∈ valBall K M) (y : K)
    {h : K} (hh : h ∈ valBall K (addCharConductor ψ - M)) :
    localFourier μ ψ f (y + h) = localFourier μ ψ f y := by sorry

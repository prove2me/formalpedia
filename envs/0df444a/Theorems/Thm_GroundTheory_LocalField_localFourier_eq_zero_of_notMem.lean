-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localFourier_eq_zero_of_notMem
-- name    : GroundTheory.LocalField.localFourier_eq_zero_of_notMem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:33:38.024072+00:00
-- url     : https://prove2.me/theorems/59faa868-f80d-4422-ae79-6b730b8ff4f1
-- title:
--   Local Field: local Fourier eq zero of not Mem
-- statement:
--   The Local Field construction uses the local Fourier eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L141-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean#L141-L158

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

theorem GroundTheory.LocalField.localFourier_eq_zero_of_notMem {f : K → ℂ} {N : ℤ}
    (hfN : ∀ x, ∀ h ∈ valBall K N, f (x + h) = f x) {y : K}
    (hy : y ∉ valBall K (addCharConductor ψ - N)) : localFourier μ ψ f y = 0 := by sorry

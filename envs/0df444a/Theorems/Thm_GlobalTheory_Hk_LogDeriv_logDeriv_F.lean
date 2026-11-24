-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LogDeriv_logDeriv_F
-- name    : GlobalTheory.Hk.LogDeriv.logDeriv_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:05.998491+00:00
-- url     : https://prove2.me/theorems/ad9e9ff4-8828-4a51-8489-6ac1f983ad0b
-- title:
--   Log Deriv: log Deriv F
-- statement:
--   The Log Deriv construction uses the log Deriv F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyLogDerivReGtOne.lean#L255-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyLogDerivReGtOne.lean#L255-L294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDeriv
open LSeries
open scoped LSeries.notation
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)

theorem GlobalTheory.Hk.LogDeriv.logDeriv_F : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 1 < s.re → LSeriesSummable (𝓕.lamChi χ) s ∧ ((s.re - 1) / s.re) ^ 2 ≤ ‖LSeries (𝓕.aChi χ) s‖ ∧ 𝓕.F χ s ≠ 0 ∧ -(deriv (𝓕.F χ) s / 𝓕.F χ s) + (if χ = 1 then 1 / (s - 1) else 0) = LSeries (𝓕.lamChi χ) s := by sorry

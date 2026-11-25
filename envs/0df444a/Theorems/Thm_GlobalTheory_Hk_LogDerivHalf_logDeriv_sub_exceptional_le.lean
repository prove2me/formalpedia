-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LogDerivHalf_logDeriv_sub_exceptional_le
-- name    : GlobalTheory.Hk.LogDerivHalf.logDeriv_sub_exceptional_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:35:31.630896+00:00
-- url     : https://prove2.me/theorems/ab6b9c05-9c62-4504-a087-d204dd83674a
-- title:
--   Log Deriv Half: log Deriv sub exceptional le
-- statement:
--   The Log Deriv Half construction uses the log Deriv sub exceptional le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivSubExceptionalLe.lean#L92-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivSubExceptionalLe.lean#L92-L260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivSubExceptionalLe
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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDerivHalf

theorem GlobalTheory.Hk.LogDerivHalf.logDeriv_sub_exceptional_le : ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 20 → ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (Z : Finset ℝ), 𝓕.ExcZ χ c₀ Z → ∀ s : ℂ, 1 - c₀ / 2 / 𝓕.ell s.im ≤ s.re → s.re ≤ 3 → (∀ β ∈ Z, s ≠ (β : ℂ)) → ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ β ∈ Z, 1 / (s - (β : ℂ))‖ ≤ C * 𝓕.ell s.im ^ 2 := by sorry

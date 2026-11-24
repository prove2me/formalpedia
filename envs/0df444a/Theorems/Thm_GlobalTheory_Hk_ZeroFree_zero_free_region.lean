-- Prove2me | Theorems.Thm_GlobalTheory_Hk_ZeroFree_zero_free_region
-- name    : GlobalTheory.Hk.ZeroFree.zero_free_region
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:36:25.433502+00:00
-- url     : https://prove2.me/theorems/cb463cda-68ff-4bed-8646-1f6d1ec481e7
-- title:
--   Zero Free: zero free region
-- statement:
--   The Zero Free construction uses the zero free region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionZeroFreeRegion.lean#L286-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionZeroFreeRegion.lean#L286-L311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionZeroFreeRegion
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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.ZeroFree

theorem GlobalTheory.Hk.ZeroFree.zero_free_region : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 3 / 4 ≤ s.re → 𝓕.F χ s = 0 → (χ * χ ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c / 𝓕.ell s.im := by sorry

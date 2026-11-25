-- Prove2me | Theorems.Thm_GlobalTheory_Hk_ZeroFree_inv_le_ell
-- name    : GlobalTheory.Hk.ZeroFree.inv_le_ell
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:03.685843+00:00
-- url     : https://prove2.me/theorems/b69883e9-61ce-436a-8d2b-14fc48400868
-- title:
--   Zero Free: inv le ell
-- statement:
--   The Zero Free construction uses the inv le ell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionZeroFreeRegion.lean#L143-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionZeroFreeRegion.lean#L143-L284

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

theorem GlobalTheory.Hk.ZeroFree.inv_le_ell : ∃ K : ℝ, 0 < K ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (ε δ γ : ℝ),
    𝓕.F χ (((1 - δ : ℝ) : ℂ) + γ * I) = 0 → (χ * χ ≠ 1 ∨ γ ≠ 0) →
    0 < ε → ε ≤ 1 / 400 → 0 ≤ δ → δ ≤ ε → 1 / ε ≤ K * 𝓕.ell γ := by sorry

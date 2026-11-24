-- Prove2me | Theorems.Thm_GlobalTheory_Hk_ZeroFree_one_le_order
-- name    : GlobalTheory.Hk.ZeroFree.one_le_order
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:18.262058+00:00
-- url     : https://prove2.me/theorems/347d636d-ce02-4ecc-8efa-c2b861f157c4
-- title:
--   Zero Free: one le order
-- statement:
--   The Zero Free construction uses the one le order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionZeroFreeRegion.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionZeroFreeRegion.lean#L22-L38

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

theorem GlobalTheory.Hk.ZeroFree.one_le_order {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} {ρ : ℂ} (h : 1 / 2 < ρ.re)
    (hρ : 𝓕.F χ ρ = 0) : 1 ≤ analyticOrderNatAt (𝓕.F χ) ρ := by sorry

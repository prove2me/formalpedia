-- Prove2me | Theorems.Thm_GlobalTheory_Hk_ZeroFree_pole_le
-- name    : GlobalTheory.Hk.ZeroFree.pole_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:36:33.213059+00:00
-- url     : https://prove2.me/theorems/7b8bd66f-58b5-426f-ae3a-0065af127362
-- title:
--   Zero Free: pole le
-- statement:
--   The Zero Free construction uses the pole le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionZeroFreeRegion.lean#L133-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionZeroFreeRegion.lean#L133-L138

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

theorem GlobalTheory.Hk.ZeroFree.pole_le {ε y : ℝ} (hε : 0 < ε) (hy : (30 * ε) ^ 2 ≤ y ^ 2) :
    6 * ε / ((6 * ε) ^ 2 + y ^ 2) ≤ 1 / 156 * (1 / ε) := by sorry

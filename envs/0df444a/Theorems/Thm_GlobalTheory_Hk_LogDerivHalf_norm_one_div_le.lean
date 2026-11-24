-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LogDerivHalf_norm_one_div_le
-- name    : GlobalTheory.Hk.LogDerivHalf.norm_one_div_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:35:20.182127+00:00
-- url     : https://prove2.me/theorems/56503183-ad23-4431-8fbd-fdf33d84faae
-- title:
--   Log Deriv Half: norm one div le
-- statement:
--   The Log Deriv Half construction uses the norm one div le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivSubExceptionalLe.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivSubExceptionalLe.lean#L79-L81

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

theorem GlobalTheory.Hk.LogDerivHalf.norm_one_div_le {z : ℂ} {r : ℝ} (hr : 0 < r) (h : r ≤ ‖z‖) : ‖1 / z‖ ≤ 1 / r := by sorry

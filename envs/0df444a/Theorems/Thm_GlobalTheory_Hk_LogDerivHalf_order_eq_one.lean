-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LogDerivHalf_order_eq_one
-- name    : GlobalTheory.Hk.LogDerivHalf.order_eq_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:35:14.174334+00:00
-- url     : https://prove2.me/theorems/2f2ff736-1a3e-4303-818b-e61766413b01
-- title:
--   Log Deriv Half: order eq one
-- statement:
--   The Log Deriv Half construction uses the order eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivSubExceptionalLe.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivSubExceptionalLe.lean#L35-L37

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

theorem GlobalTheory.Hk.LogDerivHalf.order_eq_one {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (h0 : f z = 0) (h1 : deriv f z ≠ 0) :
    analyticOrderNatAt f z = 1 := by sorry

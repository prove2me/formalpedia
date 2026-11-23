-- Prove2me | Theorems.Thm_GlobalTheory_RealZeroNearOne_analyticAt_L
-- name    : GlobalTheory.RealZeroNearOne.analyticAt_L
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:53.771257+00:00
-- url     : https://prove2.me/theorems/7d260a90-a825-4d7d-bfb9-fb61b870d8a2
-- title:
--   Real Zero Near One: analytic At L
-- statement:
--   The Real Zero Near One construction uses the analytic At L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/OrderNeTop.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/OrderNeTop.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_OrderNeTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.RealZeroNearOne

theorem GlobalTheory.RealZeroNearOne.analyticAt_L {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) (z : ℂ) :
    AnalyticAt ℂ (LFunction χ) z := by sorry

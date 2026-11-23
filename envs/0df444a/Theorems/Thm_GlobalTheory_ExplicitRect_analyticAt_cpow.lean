-- Prove2me | Theorems.Thm_GlobalTheory_ExplicitRect_analyticAt_cpow
-- name    : GlobalTheory.ExplicitRect.analyticAt_cpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:00:29.408819+00:00
-- url     : https://prove2.me/theorems/538de0d8-d628-41b6-8771-d1f17c53788a
-- title:
--   Explicit Rect: analytic At cpow
-- statement:
--   The Explicit Rect construction uses the analytic At cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AnalyticAtDslope.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AnalyticAtDslope.lean#L44-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect

theorem GlobalTheory.ExplicitRect.analyticAt_cpow {u : ℝ} (hu : 0 < u) (p : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s) p := by sorry

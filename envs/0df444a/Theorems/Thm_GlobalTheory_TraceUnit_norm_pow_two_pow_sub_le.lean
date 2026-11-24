-- Prove2me | Theorems.Thm_GlobalTheory_TraceUnit_norm_pow_two_pow_sub_le
-- name    : GlobalTheory.TraceUnit.norm_pow_two_pow_sub_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:11:30.819867+00:00
-- url     : https://prove2.me/theorems/c65750ba-77ea-4e5d-9868-a6f1aee9e4ee
-- title:
--   Trace Unit: norm pow two pow sub le
-- statement:
--   The Trace Unit construction uses the norm pow two pow sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadratic.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadratic.lean#L21-L29

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadratic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TraceUnit
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem GlobalTheory.TraceUnit.norm_pow_two_pow_sub_le {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (k : ℕ) :
    ‖x ^ 2 ^ k - y ^ 2 ^ k‖ ≤ ‖x - y‖ := by sorry

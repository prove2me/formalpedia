-- Prove2me | Theorems.Thm_GlobalTheory_TraceUnit_exists_pow_close
-- name    : GlobalTheory.TraceUnit.exists_pow_close
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:11:23.605791+00:00
-- url     : https://prove2.me/theorems/aeac06e4-0346-4c2c-a896-8072e00de560
-- title:
--   Trace Unit: exists pow close
-- statement:
--   The Trace Unit construction uses the exists pow close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadratic.lean#L60-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadratic.lean#L60-L73

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

theorem GlobalTheory.TraceUnit.exists_pow_close [ProperSpace K] {w : K} (hw : ‖w‖ ≤ 1) :
    ∃ i j : ℕ, i < j ∧ ‖w ^ 2 ^ i - w ^ 2 ^ j‖ < 1 := by sorry

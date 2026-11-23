-- Prove2me | Theorems.Thm_GlobalTheory_TraceUnit_norm_sub_le_max_of_ultra
-- name    : GlobalTheory.TraceUnit.norm_sub_le_max_of_ultra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:22.952589+00:00
-- url     : https://prove2.me/theorems/0989b954-b467-453c-ad5d-efc678d7472f
-- title:
--   Trace Unit: norm sub le max of ultra
-- statement:
--   The Trace Unit construction uses the norm sub le max of ultra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadratic.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadratic.lean#L10-L11

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

theorem GlobalTheory.TraceUnit.norm_sub_le_max_of_ultra (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by sorry

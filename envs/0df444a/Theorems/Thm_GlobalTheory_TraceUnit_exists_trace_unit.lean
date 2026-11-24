-- Prove2me | Theorems.Thm_GlobalTheory_TraceUnit_exists_trace_unit
-- name    : GlobalTheory.TraceUnit.exists_trace_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:11:24.244923+00:00
-- url     : https://prove2.me/theorems/4d9cb91b-5ede-45e1-887e-12b882c0b5cf
-- title:
--   Trace Unit: exists trace unit
-- statement:
--   The Trace Unit construction uses the exists trace unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadratic.lean#L77-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadratic.lean#L77-L175

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

theorem GlobalTheory.TraceUnit.exists_trace_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E],
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) →
      ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1 := by sorry

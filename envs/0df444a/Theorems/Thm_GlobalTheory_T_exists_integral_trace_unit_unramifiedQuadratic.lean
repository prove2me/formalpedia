-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_integral_trace_unit_unramifiedQuadratic
-- name    : GlobalTheory.T.exists_integral_trace_unit_unramifiedQuadratic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:31.612811+00:00
-- url     : https://prove2.me/theorems/5e4de26f-1707-49dd-9c8f-7347b37505e0
-- title:
--   T: exists integral trace unit unramified Quadratic
-- statement:
--   The T construction uses the exists integral trace unit unramified Quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadraticStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadraticStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadratic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadraticStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_integral_trace_unit_unramifiedQuadratic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1 := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_NTr_trace_eq
-- name    : GlobalTheory.NTr.trace_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:42.018559+00:00
-- url     : https://prove2.me/theorems/5ee7617e-f5a1-493a-8094-5bf4baf08152
-- title:
--   NTr: trace eq
-- statement:
--   The NTr construction uses the trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean#L42-L54

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]

theorem GlobalTheory.NTr.trace_eq (y : E) : algebraMap F E (Algebra.trace F E y) = y + star y := by sorry

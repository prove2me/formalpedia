-- Prove2me | Theorems.Thm_GlobalTheory_NTr_small_of_trace_small
-- name    : GlobalTheory.NTr.small_of_trace_small
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:30:11.758068+00:00
-- url     : https://prove2.me/theorems/91bf2026-ffe7-4e66-a661-1f418fd64344
-- title:
--   NTr: small of trace small
-- statement:
--   The NTr construction uses the small of trace small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean#L254-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean#L254-L270

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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]

theorem GlobalTheory.NTr.small_of_trace_small (y : E) (h : ∀ e : E, ‖e‖ ≤ 1 → ‖Algebra.trace F E (e * y)‖ < 1) : ‖y‖ < 1 := by sorry

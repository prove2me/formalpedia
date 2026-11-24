-- Prove2me | Theorems.Thm_GlobalTheory_NTr_mem_ball1
-- name    : GlobalTheory.NTr.mem_ball1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:30:10.771643+00:00
-- url     : https://prove2.me/theorems/ec8254f5-e6aa-4e85-81ed-9bfc2b4f663d
-- title:
--   NTr: mem ball1
-- statement:
--   The NTr construction uses the mem ball1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean#L71-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean#L71-L71

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem GlobalTheory.NTr.mem_ball1 {a : K} (ha : a ∈ Metric.closedBall (0 : K) 1) : ‖a‖ ≤ 1 := by sorry

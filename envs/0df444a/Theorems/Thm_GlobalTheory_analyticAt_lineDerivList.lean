-- Prove2me | Theorems.Thm_GlobalTheory_analyticAt_lineDerivList
-- name    : GlobalTheory.analyticAt_lineDerivList
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:48.561435+00:00
-- url     : https://prove2.me/theorems/784944ed-8e4f-46a9-b238-8835def74709
-- title:
--   Global Theory: analytic At line Deriv List
-- statement:
--   The Global Theory construction uses the analytic At line Deriv List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L109-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped ContDiff
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [CompleteSpace V]

theorem GlobalTheory.analyticAt_lineDerivList {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    AnalyticAt 𝕜 (lineDerivList 𝕜 l F) a := by sorry

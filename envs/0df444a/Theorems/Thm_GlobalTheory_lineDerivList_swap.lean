-- Prove2me | Theorems.Thm_GlobalTheory_lineDerivList_swap
-- name    : GlobalTheory.lineDerivList_swap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:59.612941+00:00
-- url     : https://prove2.me/theorems/d3173729-e9ee-43b3-b67d-e9b59fec10b0
-- title:
--   Global Theory: line Deriv List swap
-- statement:
--   The Global Theory construction uses the line Deriv List swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L135-L144

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

theorem GlobalTheory.lineDerivList_swap {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v w : E) :
    lineDerivList 𝕜 [v, w] F a = lineDerivList 𝕜 [w, v] F a := by sorry

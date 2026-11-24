-- Prove2me | Theorems.Thm_GlobalTheory_analyticAt_lineDeriv
-- name    : GlobalTheory.analyticAt_lineDeriv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:01.247086+00:00
-- url     : https://prove2.me/theorems/1f924ff9-b7fa-4726-a847-02e2f16d99c8
-- title:
--   Global Theory: analytic At line Deriv
-- statement:
--   The Global Theory construction uses the analytic At line Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L101-L107

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

theorem GlobalTheory.analyticAt_lineDeriv {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v : E) :
    AnalyticAt 𝕜 (fun z => lineDeriv 𝕜 F z v) a := by sorry

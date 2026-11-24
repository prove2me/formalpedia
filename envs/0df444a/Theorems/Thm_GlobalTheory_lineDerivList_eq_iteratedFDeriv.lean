-- Prove2me | Theorems.Thm_GlobalTheory_lineDerivList_eq_iteratedFDeriv
-- name    : GlobalTheory.lineDerivList_eq_iteratedFDeriv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:07:00.934974+00:00
-- url     : https://prove2.me/theorems/34659222-b065-42b2-86fd-be45a4cd7ee2
-- title:
--   Global Theory: line Deriv List eq iterated FDeriv
-- statement:
--   The Global Theory construction uses the line Deriv List eq iterated FDeriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L131-L133

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

theorem GlobalTheory.lineDerivList_eq_iteratedFDeriv {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    lineDerivList 𝕜 l F a = iteratedFDeriv 𝕜 l.length F a l.get := by sorry

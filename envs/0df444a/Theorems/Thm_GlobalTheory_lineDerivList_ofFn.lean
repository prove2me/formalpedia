-- Prove2me | Theorems.Thm_GlobalTheory_lineDerivList_ofFn
-- name    : GlobalTheory.lineDerivList_ofFn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:45.991265+00:00
-- url     : https://prove2.me/theorems/7148bb64-bb0d-4c4d-84f1-76489570d2e9
-- title:
--   Global Theory: line Deriv List of Fn
-- statement:
--   The Global Theory construction uses the line Deriv List of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L115-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L115-L129

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

theorem GlobalTheory.lineDerivList_ofFn {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {n : ℕ} (m : Fin n → E) :
    lineDerivList 𝕜 (List.ofFn m) F a = iteratedFDeriv 𝕜 n F a m := by sorry

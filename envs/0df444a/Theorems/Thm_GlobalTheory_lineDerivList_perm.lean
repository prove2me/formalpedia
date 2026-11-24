-- Prove2me | Theorems.Thm_GlobalTheory_lineDerivList_perm
-- name    : GlobalTheory.lineDerivList_perm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:02.347895+00:00
-- url     : https://prove2.me/theorems/42f7b6bd-8b07-4021-8a15-2edbb3482222
-- title:
--   Global Theory: line Deriv List perm
-- statement:
--   The Global Theory construction uses the line Deriv List perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L146-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L146-L155

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

theorem GlobalTheory.lineDerivList_perm {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {l₁ l₂ : List E}
    (hl : l₁.Perm l₂) : lineDerivList 𝕜 l₁ F a = lineDerivList 𝕜 l₂ F a := by sorry

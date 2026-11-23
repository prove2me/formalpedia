-- Prove2me | Theorems.Thm_GlobalTheory_lineDerivList_append
-- name    : GlobalTheory.lineDerivList_append
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:54.685796+00:00
-- url     : https://prove2.me/theorems/d73d6416-206a-4608-a2eb-8b359302ae5a
-- title:
--   Global Theory: line Deriv List append
-- statement:
--   The Global Theory construction uses the line Deriv List append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L25-L29

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
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {𝕜}

theorem GlobalTheory.lineDerivList_append (l₁ l₂ : List E) (F : E → V) :
    lineDerivList 𝕜 (l₁ ++ l₂) F = lineDerivList 𝕜 l₁ (lineDerivList 𝕜 l₂ F) := by sorry

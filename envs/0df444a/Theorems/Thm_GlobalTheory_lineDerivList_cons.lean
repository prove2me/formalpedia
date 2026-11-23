-- Prove2me | Theorems.Thm_GlobalTheory_lineDerivList_cons
-- name    : GlobalTheory.lineDerivList_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:45.519849+00:00
-- url     : https://prove2.me/theorems/cf6a89a9-3e0e-45e5-a166-ff9ac557494d
-- title:
--   Global Theory: line Deriv List cons
-- statement:
--   The Global Theory construction uses the line Deriv List cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L22-L23

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

theorem GlobalTheory.lineDerivList_cons (v : E) (l : List E) (F : E → V) :
    lineDerivList 𝕜 (v :: l) F = fun z => lineDeriv 𝕜 (lineDerivList 𝕜 l F) z v := by sorry

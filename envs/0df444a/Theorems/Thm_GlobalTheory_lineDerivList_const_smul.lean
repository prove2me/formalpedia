-- Prove2me | Theorems.Thm_GlobalTheory_lineDerivList_const_smul
-- name    : GlobalTheory.lineDerivList_const_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:08.450056+00:00
-- url     : https://prove2.me/theorems/0dafbf01-3742-4963-929c-c705dd955048
-- title:
--   Global Theory: line Deriv List const smul
-- statement:
--   The Global Theory construction uses the line Deriv List const smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L31-L38

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

theorem GlobalTheory.lineDerivList_const_smul (l : List E) (c : 𝕜) (F : E → V) :
    lineDerivList 𝕜 l (fun z => c • F z) = fun z => c • lineDerivList 𝕜 l F z := by sorry

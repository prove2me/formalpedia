-- Prove2me | Theorems.Thm_GlobalTheory_lineDerivList_comp_linearMap
-- name    : GlobalTheory.lineDerivList_comp_linearMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:55.151559+00:00
-- url     : https://prove2.me/theorems/e1e86cda-6eb7-49b6-97b4-82b16b4d0afb
-- title:
--   Global Theory: line Deriv List comp linear Map
-- statement:
--   The Global Theory construction uses the line Deriv List comp linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L44-L51

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

theorem GlobalTheory.lineDerivList_comp_linearMap {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    (L : E' →ₗ[𝕜] E) (l : List E') (F : E → V) :
    lineDerivList 𝕜 l (fun z => F (L z)) = fun z => lineDerivList 𝕜 (l.map L) F (L z) := by sorry

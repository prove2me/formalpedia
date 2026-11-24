-- Prove2me | Theorems.Thm_GlobalTheory_lineDerivList_add
-- name    : GlobalTheory.lineDerivList_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:38.973976+00:00
-- url     : https://prove2.me/theorems/f07162bd-2341-4152-9d85-2d5cffc3104e
-- title:
--   Global Theory: line Deriv List add
-- statement:
--   The Global Theory construction uses the line Deriv List add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L157-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L157-L165

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

theorem GlobalTheory.lineDerivList_add {F G : E → V} {a : E} (hF : AnalyticAt 𝕜 F a) (hG : AnalyticAt 𝕜 G a)
    (l : List E) :
    lineDerivList 𝕜 l (fun z => F z + G z) a
      = lineDerivList 𝕜 l F a + lineDerivList 𝕜 l G a := by sorry

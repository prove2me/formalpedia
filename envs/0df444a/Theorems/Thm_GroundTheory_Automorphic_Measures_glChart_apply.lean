-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_glChart_apply
-- name    : GroundTheory.Automorphic.Measures.glChart_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:40.243834+00:00
-- url     : https://prove2.me/theorems/2a68ff84-3ef7-5600-9d0c-91f4d1c55b64
-- title:
--   Measures: gl Chart apply
-- statement:
--   The Measures construction uses the gl Chart apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L63-L65

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

theorem GroundTheory.Automorphic.Measures.glChart_apply (g : GL (Fin n) F) (ij : Fin n × Fin n) :
    (glChart F n).toFun g ij = (g : Matrix (Fin n) (Fin n) F) ij.1 ij.2 := by sorry

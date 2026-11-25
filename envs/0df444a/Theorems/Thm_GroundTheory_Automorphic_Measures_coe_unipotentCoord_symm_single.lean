-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_coe_unipotentCoord_symm_single
-- name    : GroundTheory.Automorphic.Measures.coe_unipotentCoord_symm_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:59.909098+00:00
-- url     : https://prove2.me/theorems/c24de340-9d18-516e-8d96-9e0af9ef7faf
-- title:
--   Measures: coe unipotent Coord symm single
-- statement:
--   The Measures construction uses the coe unipotent Coord symm single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L423-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L423-L441

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}

theorem GroundTheory.Automorphic.Measures.coe_unipotentCoord_symm_single (t : UnipotentIndex n β) :
    (((unipotentCoord F n β).symm (Pi.single t 1) : lieUnipotent F n β) :
      Matrix (Fin n) (Fin n) F) = Matrix.single t.1.1 t.1.2 1 := by sorry

-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_mem_lieParabolic
-- name    : GroundTheory.Automorphic.Measures.mem_lieParabolic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:36.355744+00:00
-- url     : https://prove2.me/theorems/69b83867-e7df-5ed3-9dac-6c56930db551
-- title:
--   Measures: mem lie Parabolic
-- statement:
--   The Measures construction uses the mem lie Parabolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L24-L26

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

theorem GroundTheory.Automorphic.Measures.mem_lieParabolic {A : Matrix (Fin n) (Fin n) F} :
    A ∈ lieParabolic F n β ↔ A.BlockTriangular β := by sorry

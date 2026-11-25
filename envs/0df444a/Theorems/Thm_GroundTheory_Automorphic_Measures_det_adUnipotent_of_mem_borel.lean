-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_det_adUnipotent_of_mem_borel
-- name    : GroundTheory.Automorphic.Measures.det_adUnipotent_of_mem_borel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:07:13.272637+00:00
-- url     : https://prove2.me/theorems/9f4f6d43-0ea5-4f33-8237-accb8a25d86c
-- title:
--   Measures: det ad Unipotent of mem borel
-- statement:
--   The Measures construction uses the det ad Unipotent of mem borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L443-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L443-L487

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

theorem GroundTheory.Automorphic.Measures.det_adUnipotent_of_mem_borel (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ borel F n) :
    (LinearEquiv.det (adUnipotent p) : F) = ∏ s : UnipotentIndex n β,
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1 *
        (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2 := by sorry

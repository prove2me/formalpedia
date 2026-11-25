-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_modularCharacter_blockUpper_of_mem_borel
-- name    : GroundTheory.Automorphic.Measures.modularCharacter_blockUpper_of_mem_borel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:16.866892+00:00
-- url     : https://prove2.me/theorems/b04c133d-26f5-4bcc-8ef0-a51f1fde18a6
-- title:
--   Measures: modular Character block Upper of mem borel
-- statement:
--   The Measures construction uses the modular Character block Upper of mem borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L253-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L253-L260

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

theorem GroundTheory.Automorphic.Measures.modularCharacter_blockUpper_of_mem_borel (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ borel F n) :
    modularCharacter p = ∏ s : ParabolicIndex n β,
      modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1) /
        modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2) := by sorry

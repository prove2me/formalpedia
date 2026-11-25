-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_mulRightLie_inv
-- name    : GroundTheory.Automorphic.Measures.mulRightLie_inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:01.4225+00:00
-- url     : https://prove2.me/theorems/4c1c82cf-0717-4bab-8322-442cbc0db175
-- title:
--   Measures: mul Right Lie inv
-- statement:
--   The Measures construction uses the mul Right Lie inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L167-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L167-L173

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

theorem GroundTheory.Automorphic.Measures.mulRightLie_inv (p : blockUpper F n β) :
    mulRightLie F n β p⁻¹ = (mulRightLie F n β p)⁻¹ := by sorry

-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotent_symm
-- name    : GroundTheory.Automorphic.Measures.adUnipotent_symm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:43.956369+00:00
-- url     : https://prove2.me/theorems/cc94563b-5acb-4818-b96d-d3181ae643cc
-- title:
--   Measures: ad Unipotent symm
-- statement:
--   The Measures construction uses the ad Unipotent symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L497-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L497-L501

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

theorem GroundTheory.Automorphic.Measures.adUnipotent_symm (p : blockUpper F n β) : (adUnipotent p).symm = adUnipotent p⁻¹ := by sorry

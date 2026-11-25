-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_det_adUnipotent_of_mem_integralGL
-- name    : GroundTheory.Automorphic.Measures.distribHaarChar_det_adUnipotent_of_mem_integralGL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:00:40.80071+00:00
-- url     : https://prove2.me/theorems/c397f556-b75b-52dd-9386-cb8f3d1e4397
-- title:
--   Measures: distrib Haar Char det ad Unipotent of mem integral GL
-- statement:
--   The Measures construction uses the distrib Haar Char det ad Unipotent of mem integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L503-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L503-L529

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

theorem GroundTheory.Automorphic.Measures.distribHaarChar_det_adUnipotent_of_mem_integralGL (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ GLnLocal.integralGL F n) :
    distribHaarChar F (LinearEquiv.det (adUnipotent p)) = 1 := by sorry

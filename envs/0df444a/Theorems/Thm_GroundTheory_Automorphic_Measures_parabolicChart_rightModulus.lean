-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_parabolicChart_rightModulus
-- name    : GroundTheory.Automorphic.Measures.parabolicChart_rightModulus
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:05:03.074365+00:00
-- url     : https://prove2.me/theorems/c6920561-0d24-5818-8106-1547943bb42d
-- title:
--   Measures: parabolic Chart right Modulus
-- statement:
--   The Measures construction uses the parabolic Chart right Modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L160-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L160-L165

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

theorem GroundTheory.Automorphic.Measures.parabolicChart_rightModulus (p : blockUpper F n β) :
    (parabolicChart F n β).rightModulus p =
      distribHaarChar F (LinearEquiv.det (mulRightLie F n β p)) := by sorry

-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_map_mul_right_haarParabolic
-- name    : GroundTheory.Automorphic.Measures.map_mul_right_haarParabolic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:01.004684+00:00
-- url     : https://prove2.me/theorems/39fe8581-d4f1-44bc-b6b3-01d6e1d64700
-- title:
--   Measures: map mul right haar Parabolic
-- statement:
--   The Measures construction uses the map mul right haar Parabolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L590-L594
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L590-L594

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
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable (μ₀ : Measure (ParabolicIndex n β → F)) [μ₀.IsAddHaarMeasure]

theorem GroundTheory.Automorphic.Measures.map_mul_right_haarParabolic (p : blockUpper F n β) :
    map (· * p) (haarParabolic μ₀) =
      distribHaarChar F (LinearEquiv.det (adLie F n β p)) • haarParabolic μ₀ := by sorry

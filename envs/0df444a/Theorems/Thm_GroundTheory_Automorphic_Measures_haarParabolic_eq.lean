-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_haarParabolic_eq
-- name    : GroundTheory.Automorphic.Measures.haarParabolic_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:33.234522+00:00
-- url     : https://prove2.me/theorems/6d50afae-02e7-4a4b-a9c2-155070058fd6
-- title:
--   Measures: haar Parabolic eq
-- statement:
--   The Measures construction uses the haar Parabolic eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L581-L588
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L581-L588

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

theorem GroundTheory.Automorphic.Measures.haarParabolic_eq :
    haarParabolic μ₀ = (μ₀.comap fun (p : blockUpper F n β) (s : ParabolicIndex n β) =>
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2).withDensity
        fun p => (((distribHaarChar F (LinearEquiv.det (mulLeftLie F n β p)))⁻¹ : ℝ≥0) : ℝ≥0∞) := by sorry

-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_haarGL_eq
-- name    : GroundTheory.Automorphic.Measures.haarGL_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:54.463939+00:00
-- url     : https://prove2.me/theorems/073f26a8-265f-5884-9142-1b32b9ac5245
-- title:
--   Measures: haar GL eq
-- statement:
--   The Measures construction uses the haar GL eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L239-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L239-L246

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable (μ₀ : Measure (Fin n × Fin n → F)) [μ₀.IsAddHaarMeasure]

theorem GroundTheory.Automorphic.Measures.haarGL_eq :
    haarGL F n μ₀ = (μ₀.comap fun (g : GL (Fin n) F) (ij : Fin n × Fin n) =>
      (g : Matrix (Fin n) (Fin n) F) ij.1 ij.2).withDensity
        fun g => (((distribHaarChar F (Matrix.GeneralLinearGroup.det g) ^ n)⁻¹ : ℝ≥0) : ℝ≥0∞) := by sorry

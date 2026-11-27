-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_eq_smul_haarGL
-- name    : GroundTheory.Automorphic.Measures.eq_smul_haarGL
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:47.26314+00:00
-- url     : https://prove2.me/theorems/b520b1c2-3900-513a-8448-32e6ddca5367
-- title:
--   Measures: eq smul haar GL
-- statement:
--   The Measures construction uses the eq smul haar GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L254-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L254-L256

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

theorem GroundTheory.Automorphic.Measures.eq_smul_haarGL (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    μ = haarScalarFactor μ (haarGL F n μ₀) • haarGL F n μ₀ := by sorry

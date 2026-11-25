-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_measure_doubleCoset
-- name    : GroundTheory.Automorphic.Measures.measure_doubleCoset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:48.465888+00:00
-- url     : https://prove2.me/theorems/1d1e029e-e01d-4c02-bf5d-540f4370d925
-- title:
--   Measures: measure double Coset
-- statement:
--   The Measures construction uses the measure double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L132-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L132-L175

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem GroundTheory.Automorphic.Measures.measure_doubleCoset (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (g : G) :
    μ (doubleCoset g (K : Set G) K) =
      ((K.map (MulAut.conj g).toMonoidHom).relIndex K : ℝ≥0∞) * μ K := by sorry

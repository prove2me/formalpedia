-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_measure_preimage_mk_finset
-- name    : GroundTheory.Automorphic.Measures.measure_preimage_mk_finset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:26.176778+00:00
-- url     : https://prove2.me/theorems/50887965-c15b-5a78-b6f3-c0fd62249c57
-- title:
--   Measures: measure preimage mk finset
-- statement:
--   The Measures construction uses the measure preimage mk finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L107-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L107-L126

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

theorem GroundTheory.Automorphic.Measures.measure_preimage_mk_finset (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) (O : Finset (G ⧸ K)) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' (O : Set (G ⧸ K))) = O.card * μ K := by sorry

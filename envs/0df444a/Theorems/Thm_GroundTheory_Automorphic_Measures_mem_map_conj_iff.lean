-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_mem_map_conj_iff
-- name    : GroundTheory.Automorphic.Measures.mem_map_conj_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:55.396059+00:00
-- url     : https://prove2.me/theorems/c491d067-967f-5d1a-ac8c-9705b7be248b
-- title:
--   Measures: mem map conj iff
-- statement:
--   The Measures construction uses the mem map conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L128-L130

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

theorem GroundTheory.Automorphic.Measures.mem_map_conj_iff {K : Subgroup G} {g k : G} :
    k ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * k * g ∈ K := by sorry

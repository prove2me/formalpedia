-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_inv_doubleCoset
-- name    : GroundTheory.Automorphic.Measures.inv_doubleCoset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:25.7448+00:00
-- url     : https://prove2.me/theorems/e34b7204-14f3-5e33-aaca-9e289464f272
-- title:
--   Measures: inv double Coset
-- statement:
--   The Measures construction uses the inv double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L205-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresGL.lean#L205-L213

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

theorem GroundTheory.Automorphic.Measures.inv_doubleCoset {G : Type*} [Group G] (g : G) (K : Subgroup G) :
    (doubleCoset g (K : Set G) K)⁻¹ = doubleCoset g⁻¹ (K : Set G) K := by sorry

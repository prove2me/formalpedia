-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_fixedProj_mem_subrep
-- name    : GroundTheory.Automorphic.Whittaker.fixedProj_mem_subrep
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:08:02.774995+00:00
-- url     : https://prove2.me/theorems/fb7b550c-098d-44df-acb3-3c861762e697
-- title:
--   Whittaker: fixed Proj mem subrep
-- statement:
--   The Whittaker construction uses the fixed Proj mem subrep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L396-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L396-L407

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.Whittaker.fixedProj_mem_subrep (hρ : IsSmooth ρ) (W : Subrepresentation ρ) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) {x : V} (hx : x ∈ W) :
    ((fixedProj ρ hρ hKc hKo x : fixedVectors ρ K) : V) ∈ W := by sorry

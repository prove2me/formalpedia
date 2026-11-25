-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_annihilatorSubrep
-- name    : GroundTheory.Automorphic.Whittaker.mem_annihilatorSubrep
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:26.607157+00:00
-- url     : https://prove2.me/theorems/d2a6d3c9-4d2a-5169-9806-c98e24362cc6
-- title:
--   Whittaker: mem annihilator Subrep
-- statement:
--   The Whittaker construction uses the mem annihilator Subrep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L369-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L369-L371

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
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Automorphic.Whittaker.mem_annihilatorSubrep {W : Subrepresentation (contragredient ρ)} {v : V} :
    v ∈ annihilatorSubrep W ↔ ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) v = 0 := by sorry

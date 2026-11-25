-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_eq_top_of_annihilator_eq_bot
-- name    : GroundTheory.Automorphic.Whittaker.eq_top_of_annihilator_eq_bot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:04:56.682251+00:00
-- url     : https://prove2.me/theorems/8987f6d7-67c5-40b8-9990-b7c351d33d74
-- title:
--   Whittaker: eq top of annihilator eq bot
-- statement:
--   The Whittaker construction uses the eq top of annihilator eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L430-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L430-L462

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

theorem GroundTheory.Automorphic.Whittaker.eq_top_of_annihilator_eq_bot (h : IsAdmissible ρ) {W : Subrepresentation (contragredient ρ)}
    (hA : annihilatorSubrep W = ⊥) : W = ⊤ := by sorry

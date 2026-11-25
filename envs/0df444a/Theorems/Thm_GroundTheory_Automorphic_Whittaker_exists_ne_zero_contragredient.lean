-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_ne_zero_contragredient
-- name    : GroundTheory.Automorphic.Whittaker.exists_ne_zero_contragredient
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:06:20.617079+00:00
-- url     : https://prove2.me/theorems/125e0d34-c699-4bb6-90d9-20394baa1b0a
-- title:
--   Whittaker: exists ne zero contragredient
-- statement:
--   The Whittaker construction uses the exists ne zero contragredient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L373-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L373-L382

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

theorem GroundTheory.Automorphic.Whittaker.exists_ne_zero_contragredient (h : IsAdmissible ρ) {v : V} (hv : v ≠ 0) :
    ∃ ξ : smoothVectors (Representation.dual ρ), (ξ : Module.Dual ℂ V) v ≠ 0 := by sorry

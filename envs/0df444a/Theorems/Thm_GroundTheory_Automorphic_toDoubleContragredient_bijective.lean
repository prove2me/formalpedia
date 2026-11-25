-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_toDoubleContragredient_bijective
-- name    : GroundTheory.Automorphic.toDoubleContragredient_bijective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:25:24.600639+00:00
-- url     : https://prove2.me/theorems/712b26ad-916a-4238-b489-373b996977b4
-- title:
--   Automorphic: to Double Contragredient bijective
-- statement:
--   The Automorphic construction uses the to Double Contragredient bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L155-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L155-L193

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
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
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.toDoubleContragredient_bijective (h : IsAdmissible ρ) :
    Function.Bijective (toDoubleContragredient h.1) := by sorry

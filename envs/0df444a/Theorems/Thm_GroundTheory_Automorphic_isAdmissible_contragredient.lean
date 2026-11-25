-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isAdmissible_contragredient
-- name    : GroundTheory.Automorphic.isAdmissible_contragredient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:32.324795+00:00
-- url     : https://prove2.me/theorems/6e3a3153-1ee9-459c-a9b1-0a61882fb0c1
-- title:
--   Automorphic: is Admissible contragredient
-- statement:
--   The Automorphic construction uses the is Admissible contragredient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L150-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L150-L153

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

theorem GroundTheory.Automorphic.isAdmissible_contragredient (h : IsAdmissible ρ) : IsAdmissible (contragredient ρ) := by sorry

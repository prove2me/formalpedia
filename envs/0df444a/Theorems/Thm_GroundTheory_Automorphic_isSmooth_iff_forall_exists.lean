-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isSmooth_iff_forall_exists
-- name    : GroundTheory.Automorphic.isSmooth_iff_forall_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:44.996217+00:00
-- url     : https://prove2.me/theorems/a6fc66b7-ca54-48cc-8b3d-f43e71e88394
-- title:
--   Automorphic: is Smooth iff forall exists
-- statement:
--   The Automorphic construction uses the is Smooth iff forall exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L234-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L234-L237

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
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
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

theorem GroundTheory.Automorphic.isSmooth_iff_forall_exists :
    IsSmooth ρ ↔ ∀ v : V, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧
      v ∈ fixedVectors ρ K := by sorry

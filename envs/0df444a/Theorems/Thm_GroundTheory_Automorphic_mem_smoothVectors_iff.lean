-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_smoothVectors_iff
-- name    : GroundTheory.Automorphic.mem_smoothVectors_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:35.471219+00:00
-- url     : https://prove2.me/theorems/4e72984a-6c38-4445-9bba-24d1ed6c2f5b
-- title:
--   Automorphic: mem smooth Vectors iff
-- statement:
--   The Automorphic construction uses the mem smooth Vectors iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L223-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L223-L232

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

theorem GroundTheory.Automorphic.mem_smoothVectors_iff {v : V} :
    v ∈ smoothVectors ρ ↔ ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧
      v ∈ fixedVectors ρ K := by sorry

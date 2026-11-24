-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors
-- name    : GroundTheory.Automorphic.mem_fixedVectors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:21.104592+00:00
-- url     : https://prove2.me/theorems/286be0fa-0d3b-4f8f-b249-2ad4fb1b76a8
-- title:
--   Automorphic: mem fixed Vectors
-- statement:
--   The Automorphic construction uses the mem fixed Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L29-L30

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
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
variable {ρ}

theorem GroundTheory.Automorphic.mem_fixedVectors {H : Subgroup G} {v : V} :
    v ∈ fixedVectors ρ H ↔ ∀ h ∈ H, ρ h v = v := by sorry

-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors_iff_le
-- name    : GroundTheory.Automorphic.mem_fixedVectors_iff_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:45.38032+00:00
-- url     : https://prove2.me/theorems/a9e55f78-30fc-4c21-aaf2-885025877990
-- title:
--   Automorphic: mem fixed Vectors iff le
-- statement:
--   The Automorphic construction uses the mem fixed Vectors iff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L33-L34

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

theorem GroundTheory.Automorphic.mem_fixedVectors_iff_le {H : Subgroup G} {v : V} :
    v ∈ fixedVectors ρ H ↔ H ≤ stabilizerOf ρ v := by sorry

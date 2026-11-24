-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_act
-- name    : GroundTheory.Automorphic.fixedProj_apply_act
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:37.751694+00:00
-- url     : https://prove2.me/theorems/b3fa1f69-c9cd-47b9-9927-0f7d83ddb550
-- title:
--   Automorphic: fixed Proj apply act
-- statement:
--   The Automorphic construction uses the fixed Proj apply act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L364-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L364-L367

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
variable {ρ} {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo

theorem GroundTheory.Automorphic.fixedProj_apply_act {k : G} (hk : k ∈ K) (v : V) :
    fixedProj ρ hρ hKc hKo (ρ k v) = fixedProj ρ hρ hKc hKo v := by sorry

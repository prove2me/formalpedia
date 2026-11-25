-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_OpenNormalSubgroup_hasBasis_nhds_one_pi
-- name    : GroundTheory.ProfCoh.OpenNormalSubgroup.hasBasis_nhds_one_pi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:01.976806+00:00
-- url     : https://prove2.me/theorems/6078eeab-c1af-4743-957b-4bee81b1ab72
-- title:
--   Open Normal Subgroup: has Basis nhds one pi
-- statement:
--   The Open Normal Subgroup construction uses the has Basis nhds one pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OpenNormal.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OpenNormal.lean#L37-L45

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G]
open GroundTheory.ProfCoh.OpenNormalSubgroup
variable [IsTopologicalGroup G]
variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem GroundTheory.ProfCoh.OpenNormalSubgroup.hasBasis_nhds_one_pi (ι : Type*) [Finite ι] :
    (𝓝 (1 : ι → G)).HasBasis (fun _ : OpenNormalSubgroup G => True)
      (fun U => Set.univ.pi fun _ => (U : Set G)) := by sorry

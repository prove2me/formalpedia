-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_OpenNormalSubgroup_hasBasis_nhds_one
-- name    : GroundTheory.ProfCoh.OpenNormalSubgroup.hasBasis_nhds_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:39.190815+00:00
-- url     : https://prove2.me/theorems/83bb3eda-6d0b-44a8-be68-b784a323e476
-- title:
--   Open Normal Subgroup: has Basis nhds one
-- statement:
--   The Open Normal Subgroup construction uses the has Basis nhds one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OpenNormal.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/OpenNormal.lean#L30-L35

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

theorem GroundTheory.ProfCoh.OpenNormalSubgroup.hasBasis_nhds_one :
    (𝓝 (1 : G)).HasBasis (fun _ : OpenNormalSubgroup G => True) (fun U => (U : Set G)) := by sorry

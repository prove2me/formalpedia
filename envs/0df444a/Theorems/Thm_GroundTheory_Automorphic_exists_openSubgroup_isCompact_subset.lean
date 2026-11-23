-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset
-- name    : GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:48.0908+00:00
-- url     : https://prove2.me/theorems/ea8268f0-df44-409b-836d-e7168dc31f9e
-- title:
--   Automorphic: exists open Subgroup is Compact subset
-- statement:
--   The Automorphic construction uses the exists open Subgroup is Compact subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean#L28-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean#L28-L52

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
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
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by sorry

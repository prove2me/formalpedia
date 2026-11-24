-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasBasis_nhds_one_compactOpenSubgroup
-- name    : GroundTheory.Automorphic.hasBasis_nhds_one_compactOpenSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:54.992726+00:00
-- url     : https://prove2.me/theorems/0c2f08ee-ea46-41bc-a767-01787c624e01
-- title:
--   Automorphic: has Basis nhds one compact Open Subgroup
-- statement:
--   The Automorphic construction uses the has Basis nhds one compact Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean#L54-L58

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

theorem GroundTheory.Automorphic.hasBasis_nhds_one_compactOpenSubgroup :
    (𝓝 (1 : G)).HasBasis (fun K : OpenSubgroup G => IsCompact (K : Set G))
      (fun K => (K : Set G)) := by sorry

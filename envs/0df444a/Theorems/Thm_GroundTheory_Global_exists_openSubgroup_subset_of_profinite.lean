-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_openSubgroup_subset_of_profinite
-- name    : GroundTheory.Global.exists_openSubgroup_subset_of_profinite
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:16.447544+00:00
-- url     : https://prove2.me/theorems/8baa487f-339f-47ee-a8d6-240d542e5dff
-- title:
--   Global: exists open Subgroup subset of profinite
-- statement:
--   The Global construction uses the exists open Subgroup subset of profinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L113-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L113-L118

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Topology Filter
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]

theorem GroundTheory.Global.exists_openSubgroup_subset_of_profinite [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] {W : Set G} (hW : W ∈ 𝓝 (1 : G)) :
    ∃ V : OpenSubgroup G, (V : Set G) ⊆ W := by sorry

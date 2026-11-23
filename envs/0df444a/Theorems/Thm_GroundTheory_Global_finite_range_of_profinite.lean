-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_range_of_profinite
-- name    : GroundTheory.Global.finite_range_of_profinite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:59.059353+00:00
-- url     : https://prove2.me/theorems/93a58cf9-f7ea-4244-b7a9-49a2ab19e164
-- title:
--   Global: finite range of profinite
-- statement:
--   The Global construction uses the finite range of profinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L126-L130

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
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Global.finite_range_of_profinite (hH : NoSmallSubgroups H) (f : G →* H) (hf : Continuous f) :
    Finite f.range := by sorry

-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isCompact_inf_left
-- name    : GroundTheory.Automorphic.isCompact_inf_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:44.668973+00:00
-- url     : https://prove2.me/theorems/e42fd066-e520-4758-8019-2ac4fe7791e2
-- title:
--   Automorphic: is Compact inf left
-- statement:
--   The Automorphic construction uses the is Compact inf left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean#L74-L77

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
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Automorphic.isCompact_inf_left {K L : OpenSubgroup G} (hK : IsCompact (K : Set G)) :
    IsCompact ((K ⊓ L : OpenSubgroup G) : Set G) := by sorry

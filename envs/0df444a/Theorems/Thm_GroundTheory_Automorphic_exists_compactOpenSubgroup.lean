-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_compactOpenSubgroup
-- name    : GroundTheory.Automorphic.exists_compactOpenSubgroup
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:48.737367+00:00
-- url     : https://prove2.me/theorems/a7f6012e-700c-4a20-b83a-b02eade3f7be
-- title:
--   Automorphic: exists compact Open Subgroup
-- statement:
--   The Automorphic construction uses the exists compact Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean#L68-L70

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

theorem GroundTheory.Automorphic.exists_compactOpenSubgroup : ∃ K : OpenSubgroup G, IsCompact (K : Set G) := by sorry

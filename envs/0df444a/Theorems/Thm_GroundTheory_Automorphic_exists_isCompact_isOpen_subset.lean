-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_isCompact_isOpen_subset
-- name    : GroundTheory.Automorphic.exists_isCompact_isOpen_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:43.726004+00:00
-- url     : https://prove2.me/theorems/ab707744-e859-44ed-ad39-43116f87126f
-- title:
--   Automorphic: exists is Compact is Open subset
-- statement:
--   The Automorphic construction uses the exists is Compact is Open subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyProfinite.lean#L15-L19

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
variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X]

theorem GroundTheory.Automorphic.exists_isCompact_isOpen_subset {x : X} {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ V : Set X, IsCompact V ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ U := by sorry

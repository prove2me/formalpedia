-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_apply_eq_of_mem_smul
-- name    : GroundTheory.Automorphic.apply_eq_of_mem_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:56.9888+00:00
-- url     : https://prove2.me/theorems/ca8a012e-54ef-4a90-aaaa-a7707ebe7a42
-- title:
--   Automorphic: apply eq of mem smul
-- statement:
--   The Automorphic construction uses the apply eq of mem smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L66-L69

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
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
open scoped Pointwise
variable {G : Type*} [Group G] {E : Type*}

theorem GroundTheory.Automorphic.apply_eq_of_mem_smul {K : Subgroup G} {f : G → E}
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) {g y : G} (hy : y ∈ g • (K : Set G)) : f y = f g := by sorry

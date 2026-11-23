-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_right
-- name    : GroundTheory.Automorphic.exists_forall_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:59.735683+00:00
-- url     : https://prove2.me/theorems/e38af88b-e812-4511-9ac0-2fa9e9ec6333
-- title:
--   Automorphic: exists forall mul right
-- statement:
--   The Automorphic construction uses the exists forall mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L112-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L112-L134

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
variable [TopologicalSpace G] [IsTopologicalGroup G] {R : Type*} [Semiring R] [AddCommMonoid E]
  [Module R E]
variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Automorphic.exists_forall_mul_right {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ g, ∀ k ∈ K, f (g * k) = f g := by sorry

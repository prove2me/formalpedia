-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_left_mul_right
-- name    : GroundTheory.Automorphic.exists_forall_mul_left_mul_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:30.002574+00:00
-- url     : https://prove2.me/theorems/b487b686-029d-4b16-aa21-216c438931a7
-- title:
--   Automorphic: exists forall mul left mul right
-- statement:
--   The Automorphic construction uses the exists forall mul left mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L145-L152

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

theorem GroundTheory.Automorphic.exists_forall_mul_left_mul_right {f : G → E}
    (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      ∀ k ∈ K, ∀ g, ∀ k' ∈ K, f (k * g * k') = f g := by sorry

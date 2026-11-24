-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_left
-- name    : GroundTheory.Automorphic.exists_forall_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:00.218805+00:00
-- url     : https://prove2.me/theorems/ccdd47c7-7661-4745-aa31-257f2fce8541
-- title:
--   Automorphic: exists forall mul left
-- statement:
--   The Automorphic construction uses the exists forall mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L136-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L136-L143

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

theorem GroundTheory.Automorphic.exists_forall_mul_left {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, ∀ g, f (k * g) = f g := by sorry

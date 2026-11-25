-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_eq_sum_indicator_coset
-- name    : GroundTheory.Automorphic.eq_sum_indicator_coset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:53.704973+00:00
-- url     : https://prove2.me/theorems/8c60bf9e-29df-4360-9a2f-dc05f5e3a69d
-- title:
--   Automorphic: eq sum indicator coset
-- statement:
--   The Automorphic construction uses the eq sum indicator coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L85-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L85-L108

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

theorem GroundTheory.Automorphic.eq_sum_indicator_coset (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f)
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f = ∑ x ∈ (finite_image_mk_tsupport K hf).toFinset,
      (x.out • (K : Set G)).indicator (fun _ => f x.out) := by sorry

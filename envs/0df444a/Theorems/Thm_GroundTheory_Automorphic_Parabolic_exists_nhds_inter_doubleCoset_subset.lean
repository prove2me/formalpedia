-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_nhds_inter_doubleCoset_subset
-- name    : GroundTheory.Automorphic.Parabolic.exists_nhds_inter_doubleCoset_subset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:16.40684+00:00
-- url     : https://prove2.me/theorems/9d63190a-1a22-491d-8243-67d762d2c407
-- title:
--   Parabolic: exists nhds inter double Coset subset
-- statement:
--   The Parabolic construction uses the exists nhds inter double Coset subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaOrbit.lean#L75-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaOrbit.lean#L75-L101

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Topology Set DoubleCoset
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SigmaCompactSpace G]
variable {P Q : Subgroup G}

theorem GroundTheory.Automorphic.Parabolic.exists_nhds_inter_doubleCoset_subset (hP : IsClosed (P : Set G))
    (hQ : IsClosed (Q : Set G)) {x : G} (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q))
    {y : G} (hy : y ∈ doubleCoset x (P : Set G) Q) {UP UQ : Set G} (hUP : UP ∈ 𝓝 (1 : G))
    (hUQ : UQ ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 y, ∀ z ∈ V, z ∈ doubleCoset x (P : Set G) Q →
      ∃ p ∈ P, p ∈ UP ∧ ∃ q ∈ Q, q ∈ UQ ∧ z = p * y * q := by sorry

-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_isCompact_subset_doubleCoset
-- name    : GroundTheory.Automorphic.Parabolic.exists_isCompact_subset_doubleCoset
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:52.573713+00:00
-- url     : https://prove2.me/theorems/ede91206-54cb-4fc1-b00b-7562b5e9f9ff
-- title:
--   Parabolic: exists is Compact subset double Coset
-- statement:
--   The Parabolic construction uses the exists is Compact subset double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaOrbit.lean#L103-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaOrbit.lean#L103-L131

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

theorem GroundTheory.Automorphic.Parabolic.exists_isCompact_subset_doubleCoset (hP : IsClosed (P : Set G))
    (hQ : IsClosed (Q : Set G)) {x : G} (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q))
    {Kc : Set G} (hK : IsCompact Kc) (hKC : Kc ⊆ doubleCoset x (P : Set G) Q) :
    ∃ L : Set G, IsCompact L ∧ L ⊆ Q ∧ ∀ z ∈ Kc, ∃ p ∈ P, ∃ l ∈ L, z = p * x * l := by sorry

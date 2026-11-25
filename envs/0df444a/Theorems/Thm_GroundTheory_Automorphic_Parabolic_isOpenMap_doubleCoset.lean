-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpenMap_doubleCoset
-- name    : GroundTheory.Automorphic.Parabolic.isOpenMap_doubleCoset
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:10.694838+00:00
-- url     : https://prove2.me/theorems/bbb7cff2-6f52-46ae-a535-37024a0461f7
-- title:
--   Parabolic: is Open Map double Coset
-- statement:
--   The Parabolic construction uses the is Open Map double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaOrbit.lean#L40-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaOrbit.lean#L40-L73

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

theorem GroundTheory.Automorphic.Parabolic.isOpenMap_doubleCoset (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G)) (x : G)
    (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q)) :
    IsOpenMap (fun pq : P × Q => (⟨(pq.1 : G) * x * pq.2,
      mem_doubleCoset.2 ⟨pq.1, pq.1.2, pq.2, pq.2.2, rfl⟩⟩ : doubleCoset x (P : Set G) Q)) := by sorry

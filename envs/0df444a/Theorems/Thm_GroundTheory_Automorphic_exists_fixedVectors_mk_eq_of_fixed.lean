-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_fixedVectors_mk_eq_of_fixed
-- name    : GroundTheory.Automorphic.exists_fixedVectors_mk_eq_of_fixed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:45.514282+00:00
-- url     : https://prove2.me/theorems/5f6a3770-4a3c-41bb-b344-604ce062d72d
-- title:
--   Automorphic: exists fixed Vectors mk eq of fixed
-- statement:
--   The Automorphic construction uses the exists fixed Vectors mk eq of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L135-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L135-L197

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {N M Nbar K : Subgroup G}
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Automorphic.exists_fixedVectors_mk_eq_of_fixed (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G))
    (hfact : ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z)
    {w : V} (hwNbar : ∀ z ∈ K ⊓ Nbar, ρ z w = w)
    (hwM : ∀ y ∈ K ⊓ M, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ y w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w) :
    ∃ x ∈ fixedVectors ρ K, Representation.Coinvariants.mk (ρ.comp N.subtype) x =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by sorry

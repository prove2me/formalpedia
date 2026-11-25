-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_fixedVectors_mk_eq
-- name    : GroundTheory.Automorphic.exists_fixedVectors_mk_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:34:44.857823+00:00
-- url     : https://prove2.me/theorems/88403baa-fe65-4dbe-bf5d-e906993779a0
-- title:
--   Automorphic: exists fixed Vectors mk eq
-- statement:
--   The Automorphic construction uses the exists fixed Vectors mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L201-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionJacquet.lean#L201-L284

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

theorem GroundTheory.Automorphic.exists_fixedVectors_mk_eq (hρ : IsAdmissible ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G))
    (hfact : ∀ k ∈ K, ∃ z ∈ K ⊓ Nbar, ∃ y ∈ K ⊓ M, ∃ x ∈ K ⊓ N, k = z * y * x)
    (a : G) (haN : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (haN' : ∀ n ∈ N, a⁻¹ * n * a ∈ N)
    (haM : ∀ y ∈ K ⊓ M, a * y = y * a)
    (haK : ∀ z ∈ K ⊓ Nbar, a⁻¹ * z * a ∈ K)
    (hlim : ∀ U ∈ 𝓝 (1 : G), ∃ m : ℕ, ∀ z ∈ K ⊓ Nbar, (a ^ m)⁻¹ * z * a ^ m ∈ U)
    {v : V} (hv : ∀ y ∈ K ⊓ M, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ y v) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) v) :
    ∃ x ∈ fixedVectors ρ K, Representation.Coinvariants.mk (ρ.comp N.subtype) x =
      Representation.Coinvariants.mk (ρ.comp N.subtype) v := by sorry

-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mk_fixedProj_eq
-- name    : GroundTheory.Automorphic.Parabolic.mk_fixedProj_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:44.45592+00:00
-- url     : https://prove2.me/theorems/41c8e85d-6bf2-423d-bf7c-0aad6d8118a7
-- title:
--   Parabolic: mk fixed Proj eq
-- statement:
--   The Parabolic construction uses the mk fixed Proj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L21-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L21-L58

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
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
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {N M Nbar K : Subgroup G}

theorem GroundTheory.Automorphic.Parabolic.mk_fixedProj_eq (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hfact : ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z)
    {w : V} (hwNbar : ∀ z ∈ K ⊓ Nbar, ρ z w = w)
    (hwM : ∀ y ∈ K ⊓ M, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ y w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w) :
    Representation.Coinvariants.mk (ρ.comp N.subtype) (fixedProj ρ hρ hKc hKo w : V) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by sorry

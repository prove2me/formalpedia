-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_exists_coordsAt
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.exists_coordsAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:58.280804+00:00
-- url     : https://prove2.me/theorems/cc71586d-7341-4a5f-b2b4-5c05b85a6444
-- title:
--   Coord Model: exists coords At
-- statement:
--   The Coord Model construction uses the exists coords At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L252-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L252-L275

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
variable [IsDomain A] [IsFractionRing A Ω]
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X}

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.exists_coordsAt {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) (hz : genPt ξ ⤳ centre z)
    (h : ∀ k, ∃ c, InChart ξ (fun i => y ⟨k, i⟩) c ⟨centre z, hz⟩) (hξ : IsCptGen ξ) :
    ∃ w, CoordsAt ξ y z w := by sorry

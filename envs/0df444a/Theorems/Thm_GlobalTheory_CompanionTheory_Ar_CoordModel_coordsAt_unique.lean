-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_coordsAt_unique
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.coordsAt_unique
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:51.705443+00:00
-- url     : https://prove2.me/theorems/e7c03cfe-5d85-4bf9-b476-c8ff44e35aa5
-- title:
--   Coord Model: coords At unique
-- statement:
--   The Coord Model construction uses the coords At unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L277-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L277-L296

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

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.coordsAt_unique {K : Type} {ι : K → Type} {y : (Σ k, ι k) → Ω} (hξ : IsCptGen ξ) {w w' : (Σ k, ι k) → R}
    (h : CoordsAt ξ y z w) (h' : CoordsAt ξ y z w') (k : K) : ∃ u : Rˣ, ∀ i, w' ⟨k, i⟩ = u * w ⟨k, i⟩ := by sorry

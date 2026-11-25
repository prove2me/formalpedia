-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_exists_coordsAt_of_coordTie
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.exists_coordsAt_of_coordTie
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:45.145503+00:00
-- url     : https://prove2.me/theorems/7bfa8901-3631-430f-9bcd-3cb33cdef047
-- title:
--   Coord Model: exists coords At of coord Tie
-- statement:
--   The Coord Model construction uses the exists coords At of coord Tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L303-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L303-L306

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

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.exists_coordsAt_of_coordTie {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (h : CoordTie o ξ x) (hz : genPt ξ ⤳ centre z) :
    ∃ w, CoordsAt ξ (K := Unit) (ι := fun _ => κ) (fun j => x j.2) z w := by sorry

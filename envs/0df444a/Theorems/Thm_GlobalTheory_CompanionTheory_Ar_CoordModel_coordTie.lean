-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_coordTie
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.coordTie
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:17:41.529142+00:00
-- url     : https://prove2.me/theorems/45c3ceee-743b-4628-b686-a1d73dacf559
-- title:
--   Coord Model: coord Tie
-- statement:
--   The Coord Model construction uses the coord Tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L136-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L136-L187

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

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.coordTie (o : Type) [CommRing o] [Algebra o A] [Algebra o Ω] [IsScalarTower o A Ω]
    {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤)
    (hA : ∀ c, x c ≠ 0 → ∀ a : A, algebraMap A Ω a ∈
      Algebra.adjoin o (Set.range fun j => algebraMap A Ω (x j) / algebraMap A Ω (x c))) :
    CoordTie o (gen A Ω) (fun j => algebraMap A Ω (x j)) := by sorry

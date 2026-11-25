-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_coordTie_two_three
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.coordTie_two_three
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:37.622964+00:00
-- url     : https://prove2.me/theorems/692464f0-4db0-514a-975b-0b6a9fe6b301
-- title:
--   Coord Model: coord Tie two three
-- statement:
--   The Coord Model construction uses the coord Tie two three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L189-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L189-L194

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

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.coordTie_two_three : CoordTie ℤ (gen ℤ ℚ) (fun j => algebraMap ℤ ℚ (![2, 3] j)) := by sorry

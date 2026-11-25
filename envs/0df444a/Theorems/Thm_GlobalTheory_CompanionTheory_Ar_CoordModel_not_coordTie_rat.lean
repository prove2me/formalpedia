-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_not_coordTie_rat
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.not_coordTie_rat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:47.070955+00:00
-- url     : https://prove2.me/theorems/68496976-e97c-4dbf-9eb1-0f43d3987a19
-- title:
--   Coord Model: not coord Tie rat
-- statement:
--   The Coord Model construction uses the not coord Tie rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L196-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L196-L208

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

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.not_coordTie_rat : ¬ CoordTie ℤ (gen ℚ ℚ) (fun _ : Unit => (1 : ℚ)) := by sorry

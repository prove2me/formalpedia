-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_spec_all
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.spec_all
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:18:06.658798+00:00
-- url     : https://prove2.me/theorems/5c02e4dc-49ff-462a-a627-f1175c2fb954
-- title:
--   Coord Model: spec all
-- statement:
--   The Coord Model construction uses the spec all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L67-L70

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

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.spec_all (q : Spec (CommRingCat.of A)) : genPt (gen A Ω) ⤳ q := by sorry

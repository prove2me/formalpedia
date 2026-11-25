-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_inFibre_iff
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.inFibre_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:37.196574+00:00
-- url     : https://prove2.me/theorems/e6a018e2-b8c8-53b7-a71a-1fae3340919c
-- title:
--   Coord Model: in Fibre iff
-- statement:
--   The Coord Model construction uses the in Fibre iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L210-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L210-L226

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

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.inFibre_iff (p : ℕ) (q : Cpt (gen A Ω)) : InFibre (gen A Ω) p q ↔ (p : A) ∈ (pr A q.1).asIdeal := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_inChart_iff
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.inChart_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:17:27.945966+00:00
-- url     : https://prove2.me/theorems/bba3df45-74f9-4408-b0e6-fe2252829266
-- title:
--   Coord Model: in Chart iff
-- statement:
--   The Coord Model construction uses the in Chart iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L120-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L120-L134

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

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.inChart_iff {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤) (c : κ) (p : Cpt (gen A Ω)) :
    InChart (gen A Ω) (fun j => algebraMap A Ω (x j)) c p ↔ x c ∉ (pr A p.1).asIdeal := by sorry

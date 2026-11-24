-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_isLoc
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.isLoc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:56.583885+00:00
-- url     : https://prove2.me/theorems/3f94d25a-784f-457a-8659-b43f30d22cf5
-- title:
--   Coord Model: is Loc
-- statement:
--   The Coord Model construction uses the is Loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L20-L23

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

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.isLoc (p : Spec (CommRingCat.of A)) :
    letI := (toSt A p).toAlgebra
    IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk p) (pr A p).asIdeal := by sorry

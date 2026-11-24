-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_genMap_toSt
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.genMap_toSt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:27.797596+00:00
-- url     : https://prove2.me/theorems/0be18e4b-3313-4326-b1df-4c9560515b31
-- title:
--   Coord Model: gen Map to St
-- statement:
--   The Coord Model construction uses the gen Map to St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L26-L38

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
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.genMap_toSt (p : Cpt (gen A Ω)) (a : A) :
    genMap (gen A Ω) p (toSt A p.1 a) = algebraMap A Ω a := by sorry

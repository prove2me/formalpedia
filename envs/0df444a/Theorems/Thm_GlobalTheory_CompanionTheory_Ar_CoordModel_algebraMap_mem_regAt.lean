-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordModel_algebraMap_mem_regAt
-- name    : GlobalTheory.CompanionTheory.Ar.CoordModel.algebraMap_mem_regAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:34.885667+00:00
-- url     : https://prove2.me/theorems/b9373073-93c4-414b-9333-c952d3b67fd2
-- title:
--   Coord Model: algebra Map mem reg At
-- statement:
--   The Coord Model construction uses the algebra Map mem reg At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean#L117-L118

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
omit [IsDomain A] [IsFractionRing A Ω]

theorem GlobalTheory.CompanionTheory.Ar.CoordModel.algebraMap_mem_regAt (p : Cpt (gen A Ω)) (a : A) : algebraMap A Ω a ∈ regAt (gen A Ω) p := by sorry

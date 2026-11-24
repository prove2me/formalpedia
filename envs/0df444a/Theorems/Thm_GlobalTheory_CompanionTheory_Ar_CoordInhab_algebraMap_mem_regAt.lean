-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_algebraMap_mem_regAt
-- name    : GlobalTheory.CompanionTheory.Ar.CoordInhab.algebraMap_mem_regAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:39.710859+00:00
-- url     : https://prove2.me/theorems/bc56d4eb-a871-4280-90f3-db6fe4d5a5ca
-- title:
--   Coord Inhab: algebra Map mem reg At
-- statement:
--   The Coord Inhab construction uses the algebra Map mem reg At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean#L42-L44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory CptModel
open GlobalTheory.CompanionTheory.Ar.CoordInhab
variable {o K : Type} [CommRing o] [Field K] [Algebra o K]

theorem GlobalTheory.CompanionTheory.Ar.CoordInhab.algebraMap_mem_regAt (p : Cpt (pt (algebraMap o K))) (a : o) :
    algebraMap o K a ∈ regAt (pt (algebraMap o K)) p := by sorry

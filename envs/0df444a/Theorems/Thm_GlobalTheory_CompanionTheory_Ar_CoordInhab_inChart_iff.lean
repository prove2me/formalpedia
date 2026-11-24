-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_inChart_iff
-- name    : GlobalTheory.CompanionTheory.Ar.CoordInhab.inChart_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:51.344261+00:00
-- url     : https://prove2.me/theorems/07497938-f75c-4b7c-a2f3-d943cbfb0d5e
-- title:
--   Coord Inhab: in Chart iff
-- statement:
--   The Coord Inhab construction uses the in Chart iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean#L54-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean#L54-L76

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
variable [IsFractionRing o K]

theorem GlobalTheory.CompanionTheory.Ar.CoordInhab.inChart_iff {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (p : Cpt (pt (algebraMap o K))) :
    InChart (pt (algebraMap o K)) (fun j => algebraMap o K (x j)) c p ↔ x c ∉ p.1.asIdeal := by sorry

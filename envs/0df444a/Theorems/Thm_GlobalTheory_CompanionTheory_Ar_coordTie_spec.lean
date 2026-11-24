-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_coordTie_spec
-- name    : GlobalTheory.CompanionTheory.Ar.coordTie_spec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:46.2428+00:00
-- url     : https://prove2.me/theorems/834da2da-c8a1-48f8-a5ce-95ff509d78fc
-- title:
--   Ar: coord Tie spec
-- statement:
--   The Ar construction uses the coord Tie spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean#L109-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean#L109-L161

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
open CoordInhab

theorem GlobalTheory.CompanionTheory.Ar.coordTie_spec (o K : Type) [CommRing o] [IsDomain o] [Field K] [Algebra o K] [IsFractionRing o K]
    {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) :
    CoordTie o (Spec.map (CommRingCat.ofHom (algebraMap o K))) (fun j => algebraMap o K (x j)) := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_exists_pow_mul_eq
-- name    : GlobalTheory.CompanionTheory.Ar.CoordInhab.exists_pow_mul_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:17:31.688732+00:00
-- url     : https://prove2.me/theorems/4040a571-bf8a-40ca-991a-9175583b1e20
-- title:
--   Coord Inhab: exists pow mul eq
-- statement:
--   The Coord Inhab construction uses the exists pow mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean#L78-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean#L78-L101

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

theorem GlobalTheory.CompanionTheory.Ar.CoordInhab.exists_pow_mul_eq (t : o) (a : K)
    (h : ∀ p : Cpt (pt (algebraMap o K)), t ∉ p.1.asIdeal → a ∈ regAt (pt (algebraMap o K)) p) :
    ∃ (n : ℕ) (b : o), a * algebraMap o K t ^ n = algebraMap o K b := by sorry

-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_specializes_of_injective
-- name    : GlobalTheory.CompanionTheory.Ar.ProjCoord.specializes_of_injective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:19:09.097828+00:00
-- url     : https://prove2.me/theorems/89ccca6b-2b28-4675-ae30-965d44db8552
-- title:
--   Proj Coord: specializes of injective
-- statement:
--   The Proj Coord construction uses the specializes of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L57-L62

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]

theorem GlobalTheory.CompanionTheory.Ar.ProjCoord.specializes_of_injective (φ : A →+* Ω) (hφ : Function.Injective φ)
    (q : Spec (CommRingCat.of A)) : genPt (CptModel.pt φ) ⤳ q := by sorry

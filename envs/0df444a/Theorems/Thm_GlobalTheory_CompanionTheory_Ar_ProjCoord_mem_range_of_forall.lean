-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_mem_range_of_forall
-- name    : GlobalTheory.CompanionTheory.Ar.ProjCoord.mem_range_of_forall
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:43.812852+00:00
-- url     : https://prove2.me/theorems/27686387-48bc-423a-8962-760fa9998f49
-- title:
--   Proj Coord: mem range of forall
-- statement:
--   The Proj Coord construction uses the mem range of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L74-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L74-L94

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

theorem GlobalTheory.CompanionTheory.Ar.ProjCoord.mem_range_of_forall (φ : A →+* Ω) (c : Ω)
    (h : ∀ q : PrimeSpectrum A, ∃ a s : A, s ∉ q.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a) :
    c ∈ φ.range := by sorry

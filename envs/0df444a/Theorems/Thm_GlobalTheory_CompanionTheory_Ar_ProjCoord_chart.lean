-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_chart
-- name    : GlobalTheory.CompanionTheory.Ar.ProjCoord.chart
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:59.052315+00:00
-- url     : https://prove2.me/theorems/adfc245b-ff35-44bc-84d7-65a3b087eebc
-- title:
--   Proj Coord: chart
-- statement:
--   The Proj Coord construction uses the chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L64-L72

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

theorem GlobalTheory.CompanionTheory.Ar.ProjCoord.chart (ξ : Spec (CommRingCat.of Ω) ⟶ X) (φ : A →+* Ω) (hφ : Function.Injective φ)
    (f : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion f] (e : ξ = CptModel.pt φ ≫ f)
    (q : Spec (CommRingCat.of A)) :
    ∃ h : genPt ξ ⤳ f q, Function.Injective (genMap ξ ⟨f q, h⟩) ∧
      ∀ c : Ω, c ∈ regAt ξ ⟨f q, h⟩ ↔ ∃ a s : A, s ∉ q.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a := by sorry

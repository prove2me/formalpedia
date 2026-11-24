-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_awayEval_comp_awayMap
-- name    : GlobalTheory.CompanionTheory.Ar.ProjCoord.awayEval_comp_awayMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:19:14.596967+00:00
-- url     : https://prove2.me/theorems/9a4891c7-0b07-489e-9c6f-3dae53a16a48
-- title:
--   Proj Coord: away Eval comp away Map
-- statement:
--   The Proj Coord construction uses the away Eval comp away Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L114-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L114-L125

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
open HomogeneousLocalization
variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]

theorem GlobalTheory.CompanionTheory.Ar.ProjCoord.awayEval_comp_awayMap (ψ : A →+* Ω) {f g x : A} {d e : ℕ} (hd : f ∈ 𝒜 d) (he : g ∈ 𝒜 e)
    (hx : x = f * g) (hf : ψ f ≠ 0) (h0 : ψ x ≠ 0) :
    (awayEval 𝒜 ψ x h0).comp (awayMap 𝒜 he hx) = awayEval 𝒜 ψ f hf := by sorry

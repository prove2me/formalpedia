-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_series_first
-- name    : GlobalTheory.CompanionTheory.RgEisGal.series_first
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:00.739638+00:00
-- url     : https://prove2.me/theorems/d2834ff2-c1b5-44c2-8377-1d95bbfc3874
-- title:
--   Rg Eis Gal: series first
-- statement:
--   The Rg Eis Gal construction uses the series first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L46-L59

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GalleryOfTubesAndCrossing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]
variable [CompleteSpace W]

theorem GlobalTheory.CompanionTheory.RgEisGal.series_first {Γ K S : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {h : G → ℝ}
    {H : ℂ → G → (secSp K S c ρ) →L[ℂ] W} {a₀ : ℂ}
    (hH : ∀ g (w : secSp K S c ρ), H 0 g w = a₀ • sec K S c ρ g w) (z : ℂ) (g : G)
    (hs : Summable fun r : Cos (Γ ⊓ S) Γ =>
      ‖Complex.exp (z * h (rep r * g)) • H 0 (rep r * g)‖) (w : secSp K S c ρ) :
    outer Γ (Γ ⊓ S) h H (0, z) g w = a₀ • eis Γ K S c ρ (fun x => z * h x) g w := by sorry

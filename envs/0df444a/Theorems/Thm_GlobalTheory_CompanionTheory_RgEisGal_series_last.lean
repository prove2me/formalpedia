-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_series_last
-- name    : GlobalTheory.CompanionTheory.RgEisGal.series_last
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:16.318469+00:00
-- url     : https://prove2.me/theorems/b983212b-a0a2-4a8e-ae8c-ede1708f20f5
-- title:
--   Rg Eis Gal: series last
-- statement:
--   The Rg Eis Gal construction uses the series last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L61-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L61-L75

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

theorem GlobalTheory.CompanionTheory.RgEisGal.series_last {Γ K S : Subgroup G} {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]
    {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {h : G → ℝ}
    {H : ℂ → G → L →L[ℂ] W} {N : ℂ} {T : L →L[ℂ] secSp K S c ρ}
    (hT : ∀ g w, H N g w = Complex.exp (h g) • sec K S c ρ g (T w)) (u : ℂ) (g : G)
    (hs : Summable fun r : Cos (Γ ⊓ S) Γ =>
      ‖Complex.exp (u * h (rep r * g)) • H N (rep r * g)‖) (w : L) :
    outer Γ (Γ ⊓ S) h H (N, u) g w = eis Γ K S c ρ (fun x => h x + u * h x) g (T w) := by sorry

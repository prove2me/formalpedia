-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_IsHt_lin
-- name    : GlobalTheory.CompanionTheory.RgEisGal.IsHt_lin
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:15.736725+00:00
-- url     : https://prove2.me/theorems/fdf4a900-7c45-4ed0-9968-60a74dfb1ee6
-- title:
--   Rg Eis Gal: Is Ht lin
-- statement:
--   The Rg Eis Gal construction uses the Is Ht lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L26-L36

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

theorem GlobalTheory.CompanionTheory.RgEisGal.IsHt_lin {Γ K P : Subgroup G} {η₁ η₂ η : G → ℝ} (h₁ : IsHt Γ K P η₁) (h₂ : IsHt Γ K P η₂)
    (s t : ℝ) (e : ∀ g, η g = s * η₁ g + t * η₂ g) : IsHt Γ K P η := by sorry

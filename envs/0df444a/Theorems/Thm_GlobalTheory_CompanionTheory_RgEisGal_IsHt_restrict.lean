-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_IsHt_restrict
-- name    : GlobalTheory.CompanionTheory.RgEisGal.IsHt_restrict
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:27.910299+00:00
-- url     : https://prove2.me/theorems/e17383dd-383f-4d58-87cd-d59afbe04e6b
-- title:
--   Rg Eis Gal: Is Ht restrict
-- statement:
--   The Rg Eis Gal construction uses the Is Ht restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L22-L24

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

theorem GlobalTheory.CompanionTheory.RgEisGal.IsHt_restrict {Γ K P Q : Subgroup G} {η : G → ℝ} (h : IsHt Γ K Q η) (hPQ : P ≤ Q) :
    IsHt Γ K P η := by sorry

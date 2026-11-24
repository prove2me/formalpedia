-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_LeftGood_mono
-- name    : GlobalTheory.CompanionTheory.RgEisGal.LeftGood_mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:36.295238+00:00
-- url     : https://prove2.me/theorems/a211c929-9578-417c-a8ca-ffbe7d51ce4c
-- title:
--   Rg Eis Gal: Left Good mono
-- statement:
--   The Rg Eis Gal construction uses the Left Good mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L18-L20

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

theorem GlobalTheory.CompanionTheory.RgEisGal.LeftGood_mono {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : ℂ → X} {a a' : ℝ}
    (hf : LeftGood f a) (h : a' ≤ a) : LeftGood f a' := by sorry

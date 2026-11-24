-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_tube_coneA_iff
-- name    : GlobalTheory.CompanionTheory.RgEisGal.tube_coneA_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:05.829974+00:00
-- url     : https://prove2.me/theorems/e11e1f52-de9f-455a-af23-c68cbda71980
-- title:
--   Rg Eis Gal: tube cone A iff
-- statement:
--   The Rg Eis Gal construction uses the tube cone A iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L115-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L115-L116

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

theorem GlobalTheory.CompanionTheory.RgEisGal.tube_coneA_iff {r : ℝ} {m : ℂ × ℂ} : m ∈ tube (coneA r) ↔ r < m.2.re - m.1.re ∧ r < m.2.re := by sorry

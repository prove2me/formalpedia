-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_tube_coneI_iff
-- name    : GlobalTheory.CompanionTheory.RgEisGal.tube_coneI_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:58:52.464848+00:00
-- url     : https://prove2.me/theorems/7a5e9a32-308d-4cea-8dbe-02ca36ae3720
-- title:
--   Rg Eis Gal: tube cone I iff
-- statement:
--   The Rg Eis Gal construction uses the tube cone I iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L109-L110

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

theorem GlobalTheory.CompanionTheory.RgEisGal.tube_coneI_iff {r : ℝ} {m : ℂ × ℂ} : m ∈ tube (coneI r) ↔ r < m.2.re ∧ r < m.2.re + m.1.re := by sorry

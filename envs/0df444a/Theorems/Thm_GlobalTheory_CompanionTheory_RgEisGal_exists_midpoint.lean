-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_exists_midpoint
-- name    : GlobalTheory.CompanionTheory.RgEisGal.exists_midpoint
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:58:55.54694+00:00
-- url     : https://prove2.me/theorems/43a262e3-47b4-41dd-8b6e-9622ce257793
-- title:
--   Rg Eis Gal: exists midpoint
-- statement:
--   The Rg Eis Gal construction uses the exists midpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L155-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L155-L173

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
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

theorem GlobalTheory.CompanionTheory.RgEisGal.exists_midpoint (N r : ℝ) (x : ℝ × ℝ) :
    ∃ a ∈ coneI r, ∃ b ∈ Om3 N r, x = midpoint ℝ a b := by sorry
